//! A minimal library to read and write integers encoded using [LEB128].
//!
//! Unlike other LEB128 libraries there are three notable changes:
//!
//! 1. Uses [`zc_io`] instead of the standard library for `no_std`
//!    compatability. The standard library can be used through
//!    [`zc_io::IoReader`] and [`zc_io::IoWriter`] instances.
//! 2. When writing encoded integers, an internal buffer on the stack is used to
//!    possibly reduce system calls; each encoded integer makes a single call to
//!    [`write_all`]. This is particularly useful since buffered writers are
//!    frequently underutilized (and not native to [`zc_io`]).
//! 3. Methods always return how many bytes were used when reading or writing
//!    the integers, which may help in instances where that information would
//!    have to get retrospectively computed.
//!
//! If none of these changes are meaningful to you, consider another LEB128
//! project, as they would have less friction when just using the standard
//! library's I/O interfaces.
//!
//! # Examples
//!
//! Read and write unsigned integers:
//!
//! ```
//! # fn main() -> zc_io::Result<()> {
//! let mut buf = [0; 5];
//!
//! let encoded_length = mini_leb128::write_u32(buf.as_mut_slice(), 624_485)?;
//! assert_eq!(encoded_length.get(), 3);
//! assert_eq!(buf, [0xE5, 0x8E, 0x26, 0x00, 0x00]);
//!
//! let (value, bytes_read) = mini_leb128::read_u32(buf.as_slice())?;
//! assert_eq!(value, 624_485);
//! assert_eq!(bytes_read.get(), 3);
//! # Ok(())
//! # }
//! ```
//!
//! Read and write signed integers:
//!
//! ```
//! # fn main() -> zc_io::Result<()> {
//! let mut buf = [0; 5];
//!
//! let encoded_length = mini_leb128::write_i32(buf.as_mut_slice(), -123_456)?;
//! assert_eq!(encoded_length.get(), 3);
//! assert_eq!(buf, [0xC0, 0xBB, 0x78, 0x00, 0x00]);
//!
//! let (value, bytes_read) = mini_leb128::read_i32(buf.as_slice())?;
//! assert_eq!(value, -123_456);
//! assert_eq!(bytes_read.get(), 3);
//! # Ok(())
//! # }
//! ```
//!
//! [LEB128]: https://en.wikipedia.org/wiki/LEB128
//! [`zc_io::IoReader`]: https://docs.rs/zc_io/latest/zc_io/struct.IoReader.html
//! [`zc_io::IoWriter`]: https://docs.rs/zc_io/latest/zc_io/struct.IoWriter.html
//! [`write_all`]: Write::write_all

#![no_std]
#![doc(html_root_url = "https://docs.rs/mini_leb128/0.1.1")]
#![deny(missing_docs, clippy::pedantic)]

use core::{mem, num::NonZeroUsize};

use arrayvec::ArrayVec;
use zc_io::{error, Error, Read, Result, Write};

////////////////////////////////////////////////////////////////////////////////
// LEB128 constants
////////////////////////////////////////////////////////////////////////////////

const CONTINUATION_BIT: u8 = 0b1000_0000;
const SIGN_BIT: u8 = 0b0100_0000;
const VALUE_MASK: u8 = 0b0111_1111;
const VALUE_LENGTH: u32 = 7;

////////////////////////////////////////////////////////////////////////////////
// Encoding
////////////////////////////////////////////////////////////////////////////////

macro_rules! write_unsigned {
    ($writer:ident, $n:ident, $int:ty) => {{
        let mut buf = ArrayVec::<u8, { (mem::size_of::<$int>() / 4) * 5 }>::new();
        let mut bytes_written = 0;

        loop {
            #[allow(clippy::cast_possible_truncation)]
            let mut byte = ($n as u8) & VALUE_MASK;
            $n >>= VALUE_LENGTH;

            let done = $n == 0;

            if !done {
                byte |= CONTINUATION_BIT;
            }

            buf.push(byte);
            bytes_written += 1;

            if done {
                $writer.write_all(&buf)?;
                return Ok(unsafe { NonZeroUsize::new_unchecked(bytes_written) });
            }
        }
    }};
}

/// Encodes an unsigned 32-bit integer using LEB128.
///
/// Returns a [`NonZeroUsize`] that stores how many bytes it took to encode the
/// integer.
///
/// # Errors
///
/// Propagates any I/O errors originating from the writer. However, encoding the
/// integer itself is infallible.
pub fn write_u32<W>(mut writer: W, mut n: u32) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_unsigned!(writer, n, u32)
}

/// Encodes an unsigned 64-bit integer using LEB128.
///
/// Returns a [`NonZeroUsize`] that stores how many bytes it took to encode the
/// integer.
///
/// # Errors
///
/// Propagates any I/O errors originating from the writer. However, encoding the
/// integer itself is infallible.
pub fn write_u64<W>(mut writer: W, mut n: u64) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_unsigned!(writer, n, u64)
}

/// Encodes an unsigned 128-bit integer using LEB128.
///
/// Returns a [`NonZeroUsize`] that stores how many bytes it took to encode the
/// integer.
///
/// # Errors
///
/// Propagates any I/O errors originating from the writer. However, encoding the
/// integer itself is infallible.
pub fn write_u128<W>(mut writer: W, mut n: u128) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_unsigned!(writer, n, u128)
}

macro_rules! write_signed {
    ($writer:ident, $n:ident, $int:ty) => {{
        let mut buf = ArrayVec::<u8, { (mem::size_of::<$int>() / 4) * 5 }>::new();
        let mut bytes_written = 0;

        loop {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let mut byte = $n as u8;
            // preserve sign bit for further testing:
            $n >>= SIGN_BIT.trailing_zeros();

            let done = matches!($n, 0 | -1);

            if done {
                byte &= VALUE_MASK;
            } else {
                // discard sign bit
                $n >>= 1;
                byte |= CONTINUATION_BIT;
            }

            buf.push(byte);
            bytes_written += 1;

            if done {
                $writer.write_all(&buf)?;
                return Ok(unsafe { NonZeroUsize::new_unchecked(bytes_written) });
            }
        }
    }};
}

/// Encodes a signed 32-bit integer using LEB128.
///
/// Returns a [`NonZeroUsize`] that stores how many bytes it took to encode the
/// integer.
///
/// # Errors
///
/// Propagates any I/O errors originating from the writer. However, encoding the
/// integer itself is infallible.
pub fn write_i32<W>(mut writer: W, mut n: i32) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_signed!(writer, n, i32)
}

/// Encodes a signed 64-bit integer using LEB128.
///
/// Returns a [`NonZeroUsize`] that stores how many bytes it took to encode the
/// integer.
///
/// # Errors
///
/// Propagates any I/O errors originating from the writer. However, encoding the
/// integer itself is infallible.
pub fn write_i64<W>(mut writer: W, mut n: i64) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_signed!(writer, n, i64)
}

/// Encodes a signed 128-bit integer using LEB128.
///
/// Returns a [`NonZeroUsize`] that stores how many bytes it took to encode the
/// integer.
///
/// # Errors
///
/// Propagates any I/O errors originating from the writer. However, encoding the
/// integer itself is infallible.
pub fn write_i128<W>(mut writer: W, mut n: i128) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_signed!(writer, n, i128)
}

////////////////////////////////////////////////////////////////////////////////
// Decoding
////////////////////////////////////////////////////////////////////////////////

/// This consumes all of the bytes that, theoretically, are a continuation of
/// the LEB128-encoded integer. However, it has exceeded what the datatype could
/// store, so this is more so the stream isn't left in, again, theoretically, an
/// invalid state.
///
/// For instance, a developer could test for the `InvalidData` error variant and
/// substitute the value as the max that datatype could represent if it was not
/// critical. Then, resuming the data stream, it wouldn't be in the middle of
/// an oversized integer.
#[cold]
fn discard_leb128<'a, R>(mut reader: R) -> Error
where
    R: Read<'a>,
{
    loop {
        let byte = match reader.read_next() {
            Ok(b) => b,
            Err(error) => return error,
        };

        if byte & CONTINUATION_BIT == 0 {
            break;
        }
    }

    error!(
        InvalidData,
        "the LEB128-encoded integer getting read exceeded what the datatype could represent"
    )
}

macro_rules! read_unsigned {
    ($reader:expr, $int:ty) => {{
        const SIZE: u32 = mem::size_of::<$int>() as u32;

        let mut value = 0;
        let mut shift = 0;
        let mut bytes_read = 0;

        loop {
            let byte = $reader.read_next()?;
            let byte_value = <$int>::from(byte & VALUE_MASK);
            value |= byte_value << shift;

            shift += VALUE_LENGTH;
            bytes_read += 1;

            if byte & CONTINUATION_BIT == 0 {
                return Ok((value, unsafe { NonZeroUsize::new_unchecked(bytes_read) }));
            }

            if shift == SIZE * VALUE_LENGTH {
                return Err(discard_leb128(&mut $reader));
            }
        }
    }};
}

/// Decodes an unsigned 32-bit integer using LEB128.
///
/// Returns a tuple of the integer read and a [`NonZeroUsize`] that stores the
/// number of bytes read.
///
/// # Errors
///
/// Propagates any I/O errors originating from the reader. Otherwise, an
/// error kind of `InvalidData` is thrown if the integer read does not fit in
/// the integer's datatype.
pub fn read_u32<'a, R>(mut reader: R) -> Result<(u32, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_unsigned!(reader, u32)
}

/// Decodes an unsigned 64-bit integer using LEB128.
///
/// Returns a tuple of the integer read and a [`NonZeroUsize`] that stores the
/// number of bytes read.
///
/// # Errors
///
/// Propagates any I/O errors originating from the reader. Otherwise, an
/// error kind of `InvalidData` is thrown if the integer read does not fit in
/// the integer's datatype.
pub fn read_u64<'a, R>(mut reader: R) -> Result<(u64, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_unsigned!(reader, u64)
}

/// Decodes an unsigned 128-bit integer using LEB128.
///
/// Returns a tuple of the integer read and a [`NonZeroUsize`] that stores the
/// number of bytes read.
///
/// # Errors
///
/// Propagates any I/O errors originating from the reader. Otherwise, an
/// error kind of `InvalidData` is thrown if the integer read does not fit in
/// the integer's datatype.
pub fn read_u128<'a, R>(mut reader: R) -> Result<(u128, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_unsigned!(reader, u128)
}

macro_rules! read_signed {
    ($reader:expr, $int:ty) => {{
        const SIZE: u32 = mem::size_of::<$int>() as u32;

        let mut value = 0;
        let mut shift = 0;
        let mut bytes_read = 0;

        loop {
            let byte = $reader.read_next()?;
            let byte_value = <$int>::from(byte & VALUE_MASK);
            value |= byte_value << shift;

            shift += VALUE_LENGTH;
            bytes_read += 1;

            if byte & CONTINUATION_BIT == 0 {
                if shift < <$int>::BITS && byte & SIGN_BIT != 0 {
                    value |= !0 << shift;
                }
                return Ok((value, unsafe { NonZeroUsize::new_unchecked(bytes_read) }));
            }

            if shift == SIZE * VALUE_LENGTH {
                return Err(discard_leb128(&mut $reader));
            }
        }
    }};
}

/// Decodes a signed 32-bit integer using LEB128.
///
/// Returns a tuple of the integer read and a [`NonZeroUsize`] that stores the
/// number of bytes read.
///
/// # Errors
///
/// Propagates any I/O errors originating from the reader. Otherwise, an
/// error kind of `InvalidData` is thrown if the integer read does not fit in
/// the integer's datatype.
pub fn read_i32<'a, R>(mut reader: R) -> Result<(i32, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_signed!(reader, i32)
}

/// Decodes a signed 64-bit integer using LEB128.
///
/// Returns a tuple of the integer read and a [`NonZeroUsize`] that stores the
/// number of bytes read.
///
/// # Errors
///
/// Propagates any I/O errors originating from the reader. Otherwise, an
/// error kind of `InvalidData` is thrown if the integer read does not fit in
/// the integer's datatype.
pub fn read_i64<'a, R>(mut reader: R) -> Result<(i64, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_signed!(reader, i64)
}

/// Decodes a signed 128-bit integer using LEB128.
///
/// Returns a tuple of the integer read and a [`NonZeroUsize`] that stores the
/// number of bytes read.
///
/// # Errors
///
/// Propagates any I/O errors originating from the reader. Otherwise, an
/// error kind of `InvalidData` is thrown if the integer read does not fit in
/// the integer's datatype.
pub fn read_i128<'a, R>(mut reader: R) -> Result<(i128, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_signed!(reader, i128)
}

//! TODO

#![no_std]
#![deny(missing_docs, clippy::pedantic)]

use core::mem;
use core::num::NonZeroUsize;

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

/// TODO
///
/// # Errors
///
/// TODO
pub fn write_u32<W>(mut writer: W, mut n: u32) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_unsigned!(writer, n, u32)
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn write_u64<W>(mut writer: W, mut n: u64) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_unsigned!(writer, n, u64)
}

/// TODO
///
/// # Errors
///
/// TODO
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
                $writer.write_all(&[byte])?;
                return Ok(unsafe { NonZeroUsize::new_unchecked(bytes_written) });
            }
        }
    }};
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn write_i32<W>(mut writer: W, mut n: i32) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_signed!(writer, n, i32)
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn write_i64<W>(mut writer: W, mut n: i64) -> Result<NonZeroUsize>
where
    W: Write,
{
    write_signed!(writer, n, i64)
}

/// TODO
///
/// # Errors
///
/// TODO
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
/// an oversized VLQ.
#[cold]
fn discard_vlq<'a, R>(mut reader: R) -> Error
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
                return Err(discard_vlq(&mut $reader));
            }
        }
    }};
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn read_u32<'a, R>(mut reader: R) -> Result<(u32, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_unsigned!(reader, u32)
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn read_u64<'a, R>(mut reader: R) -> Result<(u64, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_unsigned!(reader, u64)
}

/// TODO
///
/// # Errors
///
/// TODO
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
                return Err(discard_vlq(&mut $reader));
            }
        }
    }};
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn read_i32<'a, R>(mut reader: R) -> Result<(i32, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_signed!(reader, i32)
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn read_i64<'a, R>(mut reader: R) -> Result<(i64, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_signed!(reader, i64)
}

/// TODO
///
/// # Errors
///
/// TODO
pub fn read_i128<'a, R>(mut reader: R) -> Result<(i128, NonZeroUsize)>
where
    R: Read<'a>,
{
    read_signed!(reader, i128)
}

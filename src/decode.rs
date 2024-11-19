use paste::paste;

use crate::{bits::BitArray, buffer::BitsReader};

#[derive(Debug, PartialEq)]
pub enum DecodeError {
    NotEnoughSpace,
    UnmachingSize,
}

pub type DecodeResult<T> = core::result::Result<T, DecodeError>;

/// `Decode` is trait that represent the object that will decode
pub trait Decode: Sized {
    fn decode(reader: &mut BitsReader<'_>) -> DecodeResult<Self>;
}

impl<const BITS: usize, const BYTES: usize> Decode for BitArray<BITS, BYTES> {
    fn decode(reader: &mut BitsReader) -> DecodeResult<Self> {
        reader.read_bits_array()
    }
}

impl<T: Decode, const N: usize> Decode for [T; N] {
    fn decode(reader: &mut BitsReader) -> DecodeResult<Self> {
        reader.read_array()
    }
}

macro_rules! decode_int {
    ($($ty:ty)*) => {$(
        impl Decode for $ty {
            fn decode(reader: &mut BitsReader) -> DecodeResult<Self> {
                paste! {
                    reader.[<read_ $ty>]()
                }
            }
        }
    )*};
}

decode_int! { u8 }
decode_int! { u16 }
decode_int! { u32 }
decode_int! { u64 }
decode_int! { u128 }

decode_int! { i8 }
decode_int! { i16 }
decode_int! { i32 }
decode_int! { i64 }
decode_int! { i128 }

#[cfg(test)]
mod tests {
    use crate::bits::{BitArray, BitSlice};
    use crate::buffer::BitsReader;

    use super::Decode;

    #[test]
    fn decode_int_from_slice() {
        let mut reader = BitsReader::new(BitSlice::new(&[0xDE, 0xAD, 0xBE, 0xEF]));
        let n = u32::decode(&mut reader);

        assert_eq!(n, Ok(0xDEADBEEF));
    }

    #[test]
    fn decode_array_from_slice() {
        #[allow(non_camel_case_types)]
        type u8x4 = [u8; 4];

        let mut reader = BitsReader::new(BitSlice::new(&[0xDE, 0xAD, 0xBE, 0xEF]));
        let n = u8x4::decode(&mut reader);

        assert_eq!(n, Ok([0xDE, 0xAD, 0xBE, 0xEF]));
    }

    #[test]
    fn decode_bitarray_from_slice() {
        let mut reader = BitsReader::new(BitSlice::new(&[0xDE, 0xAD, 0xBE, 0xEF]));
        let n = BitArray::<16, 2>::decode(&mut reader);

        assert_eq!(n, Ok(BitArray::new([0xDE, 0xAD])));
    }
}

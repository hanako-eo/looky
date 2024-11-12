use core::mem::MaybeUninit;

use crate::{
    bits::BitSlice,
    utils::minimal_bytes_size,
};

#[derive(Debug, PartialEq)]
pub enum DecodeError {
    NotEnoughSpace,
}

pub trait Decode: Sized {
    const SIZE: usize;

    fn decode(slice: &BitSlice) -> Result<Self, DecodeError>;
}

impl<T: Decode, const N: usize> Decode for [T; N] {
    const SIZE: usize = T::SIZE * N;

    fn decode(slice: &BitSlice) -> Result<Self, DecodeError> {
        let mut array = MaybeUninit::<[T; N]>::uninit();
        let ptr = array.as_mut_ptr() as *mut T;

        let (chunks, _) = slice
            .split_n_time::<N>(T::SIZE)
            .ok_or(DecodeError::NotEnoughSpace)?;

        for (i, chunk) in chunks.into_iter().map(T::decode).enumerate() {
            // SAFETY: `i` will not exceed N
            unsafe {
                ptr.add(i).write(chunk?);
            }
        }

        // SAFETY: correctly init before
        Ok(unsafe { array.assume_init() })
    }
}

macro_rules! decode_unsigned {
    ($ty:ty, $size:literal) => {
        impl Decode for $ty {
            const SIZE: usize = $size;

            fn decode(slice: &BitSlice) -> Result<Self, DecodeError> {
                let mut n: $ty = 0;
                for i in 0..minimal_bytes_size($size) {
                    n = n.overflowing_shl(8).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                }
                Ok(n)
            }
        }
    };
}

decode_unsigned! { u8, 8 }
decode_unsigned! { u16, 16 }
decode_unsigned! { u32, 32 }
decode_unsigned! { u64, 64 }
decode_unsigned! { u128, 128 }

macro_rules! decode_signed {
    ($ty:ty, $size:literal) => {
        impl Decode for $ty {
            const SIZE: usize = $size;

            fn decode(slice: &BitSlice) -> Result<Self, DecodeError> {
                let mut n: $ty = 0;
                for i in 0..minimal_bytes_size($size) {
                    n = n.overflowing_shl(8).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                }
                Ok(n)
            }
        }
    };
}

decode_signed! { i8, 8 }
decode_signed! { i16, 16 }
decode_signed! { i32, 32 }
decode_signed! { i64, 64 }
decode_signed! { i128, 128 }

#[cfg(test)]
mod tests {
    use crate::bits::{BitArray, BitSlice};

    use super::Decode;

    #[test]
    fn decode_int_from_slice() {
        let bit = BitSlice::new(&[0xDE, 0xAD, 0xBE, 0xEF]);
        let n = u32::decode(bit);

        assert_eq!(n, Ok(0xDEADBEEF));
    }

    #[test]
    fn decode_array_from_slice() {
        #[allow(non_camel_case_types)]
        type u8x4 = [u8; 4];

        let bit = BitSlice::new(&[0xDE, 0xAD, 0xBE, 0xEF]);
        let n = u8x4::decode(bit);

        assert_eq!(n, Ok([0xDE, 0xAD, 0xBE, 0xEF]));
    }
}

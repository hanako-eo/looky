use core::mem::MaybeUninit;

use crate::bits::BitSlice;

pub enum DecodeError {
    NotEnoughSpace,
}

pub trait Decode: Sized {
    const SIZE: usize;

    fn decode(slice: &BitSlice) -> Result<Self, DecodeError>;
}

impl<T: Decode, const N: usize> Decode for [T; N] {
    const SIZE: usize = T::SIZE * N * 8;

    fn decode(slice: &BitSlice) -> Result<Self, DecodeError> {
        let mut array = MaybeUninit::<[T; N]>::uninit();
        let ptr = array.as_mut_ptr() as *mut T;

        for i in 0..N {
            // SAFETY: `i` will not exceed N
            unsafe {
                ptr.add(i).write(T::decode(slice)?);
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
                for i in 0..=($size / 8) {
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
                for i in 0..=($size / 8) {
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

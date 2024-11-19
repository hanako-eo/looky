use core::mem::MaybeUninit;

use paste::paste;

use crate::bits::{BitArray, BitSlice};
use crate::decode::{Decode, DecodeError, DecodeResult};
use crate::utils::minimal_bytes_size;

pub struct BitsReader<'s> {
    slice: &'s BitSlice,
}

macro_rules! read_unsigned {
    ($ty:ty, $size:literal) => {
        paste! {
            pub fn [<read_ $ty>](&mut self) -> DecodeResult<$ty> {
                let slice = self.pick($size)?;

                let mut n: $ty = 0;
                for i in 0..minimal_bytes_size($size) {
                    n = n.overflowing_shl(8).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                }

                Ok(n)
            }

            pub fn [<read_into_ $ty>](&mut self, size: usize) -> DecodeResult<$ty> {
                assert!(size <= $size);

                let slice = self.pick($size)?;

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

macro_rules! read_signed {
    ($ty:ty, $uty:ty, $size:literal) => {
        paste! {
            pub fn [<read_ $ty>](&mut self) -> DecodeResult<$ty> {
                let slice = self.pick($size)?;

                let mut n: $ty = 0;
                for i in 0..minimal_bytes_size($size) {
                    n = n.overflowing_shl(8).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                }

                Ok(n)
            }

            pub fn [<read_into_ $ty>](&mut self, size: usize) -> DecodeResult<$ty> {
                let n = self.[<read_into_ $uty>](size)?;

                let signed_bit_mask = 0b1 << (size - 1);
                let rest_mask = signed_bit_mask - 1;
            
                Ok(((n & signed_bit_mask) << (7 - (size - 1)) | (n & rest_mask)) as $ty)
            }
        }
    };
}

impl<'s> BitsReader<'s> {
    pub fn new(slice: &'s BitSlice) -> Self {
        Self { slice }
    }

    pub fn buffer(&self) -> &BitSlice {
        self.slice
    }

    pub fn consume(&mut self, size: usize) -> bool {
        self.pick(size).is_ok()
    }

    pub fn pick(&mut self, size: usize) -> DecodeResult<&BitSlice> {
        let (chunk, slice) = self
            .slice
            .split_at(size)
            .ok_or(DecodeError::NotEnoughSpace)?;

        self.slice = slice;

        Ok(chunk)
    }

    pub fn read<T: Decode>(&mut self) -> DecodeResult<T> {
        T::decode(self)
    }

    pub fn read_u8(&mut self) -> DecodeResult<u8> {
        let slice = self.pick(8)?;

        slice.get_byte(0).ok_or(DecodeError::NotEnoughSpace)
    }

    pub fn read_into_u8(&mut self, size: usize) -> DecodeResult<u8> {
        assert!(size <= 8);

        let slice = self.pick(size)?;

        slice.get_byte(0).ok_or(DecodeError::NotEnoughSpace)
    }

    read_unsigned! { u16, 16 }
    read_unsigned! { u32, 32 }
    read_unsigned! { u64, 64 }
    read_unsigned! { u128, 128 }

    pub fn read_i8(&mut self) -> DecodeResult<i8> {
        let slice = self.pick(8)?;

        slice
            .get_byte(0)
            .map(|i| i as i8)
            .ok_or(DecodeError::NotEnoughSpace)
    }

    pub fn read_into_i8(&mut self, size: usize) -> DecodeResult<i8> {
        assert!(size <= 8);

        let slice = self.pick(size)?;

        slice
            .get_byte(0)
            .map(|i| {
                let signed_bit_mask = 0b1 << (size - 1);
                let rest_mask = signed_bit_mask - 1;

                ((i & signed_bit_mask) << (7 - (size - 1)) | (i & rest_mask)) as i8
            })
            .ok_or(DecodeError::NotEnoughSpace)
    }

    read_signed! { i16, u16, 16 }
    read_signed! { i32, u32, 32 }
    read_signed! { i64, u64, 64 }
    read_signed! { i128, u128, 128 }

    pub fn read_bits_array<const BITS: usize, const BYTES: usize>(
        &mut self,
    ) -> DecodeResult<BitArray<BITS, BYTES>> {
        let slice = self.pick(BITS)?;

        let mut array = BitArray::new([0; BYTES]);
        array
            .try_copy_from_slice(slice)
            .map_err(|_| DecodeError::UnmachingSize)?;

        Ok(array)
    }

    pub fn read_array<T: Decode, const N: usize>(&mut self) -> DecodeResult<[T; N]> {
        let mut array = MaybeUninit::<[T; N]>::uninit();
        let ptr = array.as_mut_ptr() as *mut T;

        for i in 0..N {
            let value = match T::decode(self) {
                Ok(value) => value,
                Err(err) => {
                    for j in 0..i {
                        // SAFETY: if an error has occurred, we discard all
                        // structures already initialized
                        unsafe {
                            ptr.add(j).drop_in_place();
                        }
                    }
                    return Err(err);
                }
            };
            // SAFETY: `i` will not exceed N
            unsafe {
                ptr.add(i).write(value);
            }
        }

        // SAFETY: correctly init before
        Ok(unsafe { array.assume_init() })
    }

    pub fn read_exact_slice(&mut self, result_slice: &mut BitSlice) -> DecodeResult<()> {
        let unconsumed_chunk = self.pick(result_slice.len())?;

        result_slice
            .try_copy_from_slice(unconsumed_chunk)
            .map_err(|_| DecodeError::UnmachingSize)
    }
}

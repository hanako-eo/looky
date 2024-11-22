use core::mem::MaybeUninit;

use paste::paste;

use crate::bits::{BitArray, BitSlice};
use crate::decode::{Decode, DecodeError, DecodeResult};
use crate::utils::minimal_bytes_size;

/// `BitsReader` is a reader of a bit slice and transforms the stored slice into
/// data that implements the [`Decode`] trait via the reads method like [`read`].  
pub struct BitsReader<'s> {
    slice: &'s BitSlice,
}

macro_rules! read_unsigned {
    ($ty:ty, $size:literal) => {
        paste! {
            #[doc = "Read a `" $ty "`"]
            pub fn [<read_ $ty>](&mut self) -> DecodeResult<$ty> {
                let slice = self.pick($size)?;

                let mut n: $ty = 0;
                for i in 0..minimal_bytes_size($size) {
                    n = n.overflowing_shl(8).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                }

                Ok(n)
            }

            #[doc = "Read an unsigned int smaller than a `" $ty "` of a size of `size` and store into a `" $ty "`"]
            pub fn [<read_into_ $ty>](&mut self, mut size: usize) -> DecodeResult<$ty> {
                const MIN_BYTES_SIZE: usize = $size / 8;
                assert!(size <= $size);

                let slice = self.pick(size)?;

                let mut n: $ty = 0;
                for i in 0..MIN_BYTES_SIZE {
                    n = n.overflowing_shl(size.min(8) as u32).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                    size = size.saturating_sub(8);
                }

                Ok(n)
            }
        }
    };
}

macro_rules! read_signed {
    ($ty:ty, $uty:ty, $size:literal) => {
        paste! {
            #[doc = "Read a `" $ty "`"]
            pub fn [<read_ $ty>](&mut self) -> DecodeResult<$ty> {
                let slice = self.pick($size)?;

                let mut n: $ty = 0;
                for i in 0..minimal_bytes_size($size) {
                    n = n.overflowing_shl(8).0
                        | (slice.get_byte(i).ok_or(DecodeError::NotEnoughSpace)? as $ty);
                }

                Ok(n)
            }

            #[doc = "Read an signed int smaller than a `" $ty "` of a size of `size` and store into a `" $ty "`"]
            pub fn [<read_into_ $ty>](&mut self, size: usize) -> DecodeResult<$ty> {
                let n = self.[<read_into_ $uty>](size)?;

                let signed_bit_mask = 0b1 << (size - 1);
                let rest_mask = signed_bit_mask - 1;
            
                Ok(((n & signed_bit_mask) << ($size - size) | (n & rest_mask)) as $ty)
            }
        }
    };
}

impl<'s> BitsReader<'s> {
    /// Create the reader as of a bit slice.
    pub fn new(slice: &'s BitSlice) -> Self {
        Self { slice }
    }
    
    /// Return the current state of the current slice.
    pub fn buffer(&self) -> &BitSlice {
        self.slice
    }
    
    /// Consume `size` bits and return true if it's success, false else. 
    pub fn consume(&mut self, size: usize) -> bool {
        self.pick(size).is_ok()
    }
    
    /// Try to pick a part of the buffer with a size of `size`, return `None`
    /// if the stored slice if too small. 
    pub fn pick(&mut self, size: usize) -> DecodeResult<&BitSlice> {
        let (chunk, slice) = self
            .slice
            .split_at(size)
            .ok_or(DecodeError::NotEnoughSpace)?;

        self.slice = slice;

        Ok(chunk)
    }

    /// Read a `T`.
    pub fn read<T: Decode>(&mut self) -> DecodeResult<T> {
        T::decode(self)
    }
    
    /// Read a `u8`.
    pub fn read_u8(&mut self) -> DecodeResult<u8> {
        let slice = self.pick(8)?;
        
        slice.get_byte(0).ok_or(DecodeError::NotEnoughSpace)
    }
    
    /// Read an unsigned int smaller than a `u8` of a size of `size` and store
    /// into a `u8`.
    pub fn read_into_u8(&mut self, size: usize) -> DecodeResult<u8> {
        assert!(size <= 8);

        let slice = self.pick(size)?;

        slice.get_byte(0).ok_or(DecodeError::NotEnoughSpace)
    }

    read_unsigned! { u16, 16 }
    read_unsigned! { u32, 32 }
    read_unsigned! { u64, 64 }
    read_unsigned! { u128, 128 }

    /// Read a `i8`.
    pub fn read_i8(&mut self) -> DecodeResult<i8> {
        let slice = self.pick(8)?;

        slice
            .get_byte(0)
            .map(|i| i as i8)
            .ok_or(DecodeError::NotEnoughSpace)
    }

    /// Read an unsigned int smaller than a `i8` of a size of `size` and store
    /// into a `i8`.
    pub fn read_into_i8(&mut self, size: usize) -> DecodeResult<i8> {
        assert!(size <= 8);

        let slice = self.pick(size)?;

        slice
            .get_byte(0)
            .map(|i| {
                let signed_bit_mask = 0b1 << (size - 1);
                let rest_mask = signed_bit_mask - 1;

                ((i & signed_bit_mask) << (8 - size) | (i & rest_mask)) as i8
            })
            .ok_or(DecodeError::NotEnoughSpace)
    }

    read_signed! { i16, u16, 16 }
    read_signed! { i32, u32, 32 }
    read_signed! { i64, u64, 64 }
    read_signed! { i128, u128, 128 }

    /// Read a array of bits.
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

    /// Read a array of T.
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

#[cfg(test)]
mod tests {
    use crate::bits::BitSlice;

    use super::BitsReader;

    #[test]
    fn read_u8_and_u4() {
        let mut reader = BitsReader::new(BitSlice::new(&[0xBE, 0xEF]));

        assert_eq!(reader.read_u8(), Ok(0xBE));
        assert_eq!(reader.read_into_u8(4), Ok(0xE));

        assert_eq!(reader.buffer(), BitSlice::with_size(4, &[0xF0]));
    }

    #[test]
    fn read_u12() {
        let mut reader = BitsReader::new(BitSlice::new(&[0xBE, 0xEF]));

        assert_eq!(reader.read_into_u16(12), Ok(0xBEE));

        assert_eq!(reader.buffer(), BitSlice::with_size(4, &[0xF0]));
    }

    #[test]
    fn read_i8_and_i4() {
        let mut reader = BitsReader::new(BitSlice::new(&[0xFF, 0xFF]));

        assert_eq!(reader.read_i8(), Ok(-1));
        assert_eq!(reader.read_into_i8(4), Ok(-121));

        assert_eq!(reader.buffer(), BitSlice::with_size(4, &[0xF0]));
    }

    #[test]
    fn read_i12() {
        let mut reader = BitsReader::new(BitSlice::new(&[0xFF, 0xF7]));

        // 0x87FF = 0b1000011111111111
        assert_eq!(reader.read_into_i16(12), Ok(0x87FFu16 as i16));

        assert_eq!(reader.buffer(), BitSlice::with_size(4, &[0x70]));
    }
}

use core::fmt;
use core::ops::{Deref, DerefMut};

use crate::utils::minimal_bytes_size;

use super::BitSlice;

/// `BitArray` is a struct for managing an array of bits of a specified size.
/// It uses const generic parameters to dynamically adjust the number of bits
/// and bytes needed for storage.
///
/// # Generic Parameters
///
/// - `BITS` is the total number of bits that `BitArray` should contain.
/// - `BYTES` is the number of bytes required to store these bits.
///
/// When you called the new constructor `BYTES` need to assert this equation:
///  - If `BITS` is a mutiple of 8 `BYTES = BITS / 8`
///  - Otherwise `BITS / 8 + 1`
pub struct BitArray<const BITS: usize, const BYTES: usize>([u8; BYTES]);

impl<const BITS: usize, const BYTES: usize> BitArray<BITS, BYTES> {
    pub fn new(array: [u8; BYTES]) -> Self {
        assert_eq!(minimal_bytes_size(BITS), BYTES);

        Self(array)
    }

    /// Returns a slice containing the entire array.
    pub fn as_slice(&self) -> &BitSlice {
        self
    }

    /// Returns a mutable slice containing the entire array.
    pub fn as_mut_slice(&mut self) -> &mut BitSlice {
        self
    }
}

impl<const BITS: usize, const BYTES: usize> Deref for BitArray<BITS, BYTES> {
    type Target = BitSlice;

    fn deref(&self) -> &Self::Target {
        BitSlice::with_size(BITS, &self.0)
    }
}

impl<const BITS: usize, const BYTES: usize> DerefMut for BitArray<BITS, BYTES> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        BitSlice::with_size_mut(BITS, &mut self.0)
    }
}

impl<const BITS: usize, const BYTES: usize> fmt::Debug for BitArray<BITS, BYTES> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_slice())
    }
}

impl<const BITS: usize, const BYTES1: usize, const BYTES2: usize> PartialEq<BitArray<BITS, BYTES2>>
    for BitArray<BITS, BYTES1>
{
    fn eq(&self, other: &BitArray<BITS, BYTES2>) -> bool {
        for (i, bit) in self.into_iter().enumerate() {
            // SAFETY: because self and other has the same size,
            // so the n-th bit already exist and has a value
            if bit != unsafe { other.get_unchecked(i) } {
                return false;
            }
        }

        true
    }
}

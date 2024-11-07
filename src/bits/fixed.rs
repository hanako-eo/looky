use core::ops::{Deref, DerefMut};

use super::BitSlice;

pub struct BitArray<const N: usize>([u8; N]);

impl<const N: usize> BitArray<N> {
    pub fn new(array: [u8; N]) -> Self {
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

impl<const N: usize> Deref for BitArray<N> {
    type Target = BitSlice;

    fn deref(&self) -> &Self::Target {
        BitSlice::new(&self.0)
    }
}

impl<const N: usize> DerefMut for BitArray<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        BitSlice::from_mut(&mut self.0)
    }
}

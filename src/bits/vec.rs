use core::{
    fmt,
    ops::{Deref, DerefMut},
};

use alloc::vec::Vec;

use super::{BitArray, BitSlice};

#[derive(Default)]
pub struct BitVec {
    raw: Vec<u8>,
    len: usize,
}

impl BitVec {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the capacity of the vector.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.raw.len() * 8
    }

    /// Returns the number of bits handled by the slice.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the number of bytes use by the vector.
    #[inline]
    #[must_use]
    pub fn byte_len(&self) -> usize {
        self.raw.len()
    }

    /// Check is the slice is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice containing the entire vector.
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &BitSlice {
        self
    }

    /// Returns a mutable slice containing the entire vector.
    #[inline]
    #[must_use]
    pub fn as_mut_slice(&mut self) -> &mut BitSlice {
        self
    }

    /// Appends an bit to the back of a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::{BitSlice, BitVec};
    ///
    /// let mut vec = BitVec::new();
    /// vec.push(true);
    /// vec.push(false);
    /// vec.push(true);
    ///
    /// assert_eq!(&vec, &BitSlice::with_size(3, &[0b101_00000]));
    /// ```
    pub fn push(&mut self, value: bool) {
        let len = self.len();
        if len == self.capacity() {
            self.raw.push(0);
        }

        // SAFETY: the byte exists because if `self.len() % 8 == 0` then a new
        // byte has been added previously, otherwise it will touch the last byte
        self.len += 1;

        let mut bit = unsafe { self.get_mut_unchecked(len) };
        bit.put(value);
    }

    /// Removes the last element from a vector and returns it, or None if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::{BitSlice, BitVec};
    ///
    /// let mut vec = BitVec::new();
    /// vec.push(true);
    /// vec.push(false);
    /// vec.push(true);
    ///
    /// assert_eq!(&vec, &BitSlice::with_size(3, &[0b101_00000]));
    ///
    /// let bit = vec.pop();
    ///
    /// assert_eq!(bit, Some(true));
    /// assert_eq!(&vec, &BitSlice::with_size(2, &[0b10_000000]));
    /// ```
    pub fn pop(&mut self) -> Option<bool> {
        if self.is_empty() {
            return None;
        }

        // SAFETY: the byte necessarily exists as the slice is not empty
        let bit = unsafe { self.get_unchecked(self.len() - 1) }.value();
        self.len -= 1;

        if self.len % 8 == 0 {
            self.raw.pop();
        }

        Some(bit)
    }
}

impl Deref for BitVec {
    type Target = BitSlice;

    #[inline]
    fn deref(&self) -> &Self::Target {
        BitSlice::with_size(self.len(), &self.raw)
    }
}

impl DerefMut for BitVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        BitSlice::with_size_mut(self.len(), &mut self.raw)
    }
}

impl fmt::Debug for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_slice())
    }
}

impl<T: Deref<Target = BitSlice>> PartialEq<T> for BitVec {
    fn eq(&self, other: &T) -> bool {
        self.deref() == other.deref()
    }
}

impl<const BITS: usize, const BYTES: usize> From<BitArray<BITS, BYTES>> for BitVec {
    #[inline]
    #[must_use]
    fn from(value: BitArray<BITS, BYTES>) -> Self {
        Self {
            raw: value.0.to_vec(),
            len: BITS,
        }
    }
}

impl From<&BitSlice> for BitVec {
    #[inline]
    #[must_use]
    fn from(value: &BitSlice) -> Self {
        Self {
            raw: value.0.to_vec(),
            len: value.len(),
        }
    }
}

impl From<&mut BitSlice> for BitVec {
    #[inline]
    #[must_use]
    fn from(value: &mut BitSlice) -> Self {
        Self {
            raw: value.0.to_vec(),
            len: value.len(),
        }
    }
}

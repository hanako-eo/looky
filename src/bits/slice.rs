use core::fmt;
use core::marker::PhantomData;
use core::ptr::{slice_from_raw_parts, NonNull};

use crate::slice::SliceIndex;
use crate::utils::minimal_bytes_size;

/// BitSlice works like a fat pointer, it describes a byte slice (perhaps seen
/// as equivalent to a `&[u8]`) but its purpose is to allow bit-by-bit manipulation
/// of the array.
/// 
/// Like other pointer or ref, it can be copy (the heaviest part of the copy will
/// be in the metadata copy).
#[derive(Clone, Copy)]
pub struct BitSlice<'s> {
    ptr: NonNull<u8>,
    metadata: Metadata,

    phantom: PhantomData<&'s ()>,
}

#[derive(Clone, Copy)]
pub(crate) struct Metadata {
    pub(crate) size: usize,
    pub(crate) bit_offset: u8,
}

impl<'s> BitSlice<'s> {
    #[inline]
    pub fn new<S: AsRef<[u8]> + ?Sized>(slice: &'s S) -> Self {
        Self::with_offset(0, slice)
    }

    #[inline]
    pub fn with_offset<S: AsRef<[u8]> + ?Sized>(bit_offset: u8, slice: &'s S) -> Self {
        let slice = slice.as_ref();

        Self::with_size_and_offset(bit_offset, slice.len() * 8, slice)
    }

    #[inline]
    pub fn with_size<S: AsRef<[u8]> + ?Sized>(size: usize, slice: &'s S) -> Self {
        Self::with_size_and_offset(0, size, slice)
    }

    #[inline]
    pub fn with_size_and_offset<S: AsRef<[u8]> + ?Sized>(
        bit_offset: u8,
        size: usize,
        slice: &'s S,
    ) -> Self {
        let slice = slice.as_ref();

        debug_assert!(bit_offset < 8 && size <= slice.len() * 8);

        // SAFETY: all args are checked before
        unsafe { Self::from_raw(bit_offset, size, slice.as_ptr()) }
    }

    #[inline]
    pub unsafe fn from_raw(bit_offset: u8, size: usize, ptr: *const u8) -> Self {
        Self {
            metadata: Metadata { bit_offset, size },
            ptr: unsafe { NonNull::new_unchecked(ptr as _) },

            phantom: PhantomData,
        }
    }

    #[inline]
    pub fn from_mut<S: AsMut<[u8]> + ?Sized>(slice: &mut S) -> Self {
        let slice = slice.as_mut();

        Self {
            metadata: Metadata {
                bit_offset: 0,
                size: slice.len() * 8,
            },
            ptr: unsafe { NonNull::new_unchecked(slice.as_mut_ptr()) },

            phantom: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub(crate) const fn offset(self) -> u8 {
        self.metadata.bit_offset
    }

    #[inline]
    #[must_use]
    pub const fn len(self) -> usize {
        self.metadata.size
    }

    #[inline]
    #[must_use]
    pub const fn byte_len(self) -> usize {
        minimal_bytes_size(self.len() + self.offset() as usize)
    }

    #[inline]
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[must_use]
    pub const fn first_bit(self) -> Option<bool> {
        match self.is_empty() {
            false => {
                Some(unsafe { (*self.ptr.as_ref() & (1 << (7 - self.metadata.bit_offset))) != 0 })
            }
            true => None,
        }
    }

    /// Returns the first byte of the slice, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let v = [10, 40, 30];
    /// assert_eq!(Some(&10), v.first());
    ///
    /// let w: &[i32] = &[];
    /// assert_eq!(None, w.first());
    /// ```
    #[inline]
    #[must_use]
    pub const fn first_byte(self) -> Option<u8> {
        match self.is_empty() {
            false => Some(unsafe { *self.ptr.as_ref() }),
            true => None,
        }
    }

    /// Returns a raw pointer to the slice’s buffer.
    /// 
    /// The caller must ensure that the slice outlives the pointer this function
    /// returns, or else it will end up dangling.
    /// 
    /// The caller must also ensure that the memory the pointer (non-transitively)
    /// points to is never written to (except inside an UnsafeCell) using this
    /// pointer or any pointer derived from it.
    /// 
    /// Modifying the container referenced by this slice may cause its buffer
    /// to be reallocated, which would also make any pointers to it invalid.
    #[inline]
    pub const fn as_ptr(self) -> *const u8 {
        self.ptr.as_ptr()
    }

    /// Get the origin slice store in the bit slice.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    /// 
    /// assert_eq!(unsafe { bits.get_slice() }, &[0b00101000, 0b11011111]);
    /// ```
    #[inline]
    pub const unsafe fn get_slice(self) -> &'s [u8] {
        &*slice_from_raw_parts(self.ptr.as_ptr(), self.byte_len())
    }

    /// This function get the n-th bit of the bits if the index is an integer (`usize`),
    /// otherwise if it's a range it returns a new slice that will contain the
    /// requested range.
    ///
    /// Indexs works "normally", i.e. in the same way as an array, for exemple:
    /// ```"not rust"
    /// 10011100 <- it's at the index 7
    /// ^ it's at the index 0
    /// ```
    ///
    /// # Examples
    /// 
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^ this bit
    /// assert_eq!(bits.get(2), Some(true));
    ///
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^^^^ this range of bits
    /// assert_eq!(bits.get(2..6), Some(BitSlice::with_size_and_offset(2, 4, &[0b00_1010_00])));
    /// //                                                            retrieve here ^^^^
    /// ```
    #[inline]
    pub fn get<I: SliceIndex<Self>>(self, index: I) -> Option<I::Output> {
        index.get(self)
    }

    /// This function get the n-th bit of the bits if the index is an integer (`usize`),
    /// otherwise if it's a range it returns a new slice that will contain the
    /// requested range.
    ///
    /// Indexs works "normally", i.e. in the same way as an array, for exemple:
    /// ```"not rust"
    /// 10011100 <- it's at the index 7
    /// ^ it's at the index 0
    /// ```
    ///
    /// # Examples
    /// 
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^ this bit
    /// assert_eq!(unsafe { bits.get_unchecked(2) }, true);
    ///
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^^^^ this range of bits
    /// assert_eq!(unsafe { bits.get_unchecked(2..6) }, BitSlice::with_size_and_offset(2, 4, &[0b00_1010_00]));
    /// //                                                            retrieve here ^^^^
    /// ```
    ///
    /// ```should_panic
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    ///
    /// unsafe { bits.get_unchecked(20..60) };
    /// ```
    #[inline]
    pub unsafe fn get_unchecked<I: SliceIndex<Self>>(self, index: I) -> I::Output {
        index.get_unchecked(self)
    }

    /// Returns the `index` bytes, if it's in bounts, otherwise it panics.
    ///
    /// # Examples
    /// 
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    ///
    /// // try to get the second byte
    /// assert_eq!(unsafe { bits.get_byte_unchecked(1) }, 0b11011111);
    /// ```
    ///
    /// ```should_panic
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    ///
    /// // try to get the third byte but panic
    /// unsafe { bits.get_byte_unchecked(2) };
    /// ```
    pub unsafe fn get_byte_unchecked(self, index: usize) -> u8 {
        assert!(
            index < self.byte_len(),
            "BitSlice::get_byte_unchecked requires that the index is within the slice"
        );

        *self.ptr.add(index).as_ref()
    }

    /// Returns the `index` bytes, if it's out of bounts, it will return `None`.
    ///
    /// # Examples
    /// 
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    ///
    /// // try to get the second byte
    /// assert_eq!(bits.get_byte(1), Some(0b11011111));
    /// ```
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    ///
    /// // try to get the third byte
    /// assert_eq!(bits.get_byte(2), None);
    /// ```
    pub fn get_byte(self, index: usize) -> Option<u8> {
        (index < self.byte_len()).then(|| unsafe { self.get_byte_unchecked(index) })
    }
}

impl<'s> From<&'s [u8]> for BitSlice<'s> {
    #[inline]
    fn from(slice: &'s [u8]) -> Self {
        BitSlice::new(slice)
    }
}

impl<'s> From<&'s mut [u8]> for BitSlice<'s> {
    #[inline]
    fn from(slice: &'s mut [u8]) -> Self {
        BitSlice::from_mut(slice)
    }
}

impl<'s> IntoIterator for BitSlice<'s> {
    type IntoIter = super::Iter<'s>;
    type Item = <Self::IntoIter as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        super::Iter {
            slice: self,
            index: 0,
        }
    }
}

impl<'s, 's2> PartialEq<BitSlice<'s2>> for BitSlice<'s> {
    fn eq(&self, other: &BitSlice<'s2>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        // seem to look like "a == a"
        if self.offset() == other.offset() && self.ptr == other.ptr {
            return true;
        }

        for (i, bit) in self.into_iter().enumerate() {
            // SAFETY: because self and other has the same size,
            // so the n-th bit already exist and has a value
            if bit != unsafe { other.get_unchecked(i) } {
                return false;
            }
        }

        return true;
    }
}

impl<'s> Eq for BitSlice<'s> {}

impl<'s> fmt::Debug for BitSlice<'s> {
    /// Print in debug mode the bits.
    ///
    /// # Examples
    /// 
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b10011001, 0b01100110, 0b11110000, 0b00001111]);
    ///
    /// assert_eq!(format!("{:?}", bits), String::from("0b10011001_01100110_11110000_00001111"));
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "0b0");
        }

        for (i, bit) in self.into_iter().enumerate() {
            let c = if bit { '1' } else { '0' };
            if i == 0 {
                write!(f, "0b{c}")?;
            } else if i % 8 == 0 {
                write!(f, "_{c}")?;
            } else {
                write!(f, "{c}")?;
            }
        }
        Ok(())
    }
}

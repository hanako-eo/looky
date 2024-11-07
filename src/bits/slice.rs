use core::fmt;

use crate::slice::SliceIndex;
use crate::utils::minimal_bytes_size;

use super::metadata::{half_usize, Metadata};

/// BitSlice works like a fat pointer, it describes a byte slice (perhaps seen
/// as equivalent to a `&[u8]`) but its purpose is to allow bit-by-bit manipulation
/// of the array.
pub struct BitSlice([u8]);

// TODO: add more constructor of `&mut BitSlice`
impl BitSlice {
    /// Create a bit slice from a slice.
    ///
    /// # Example
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b10101010]);
    /// ```
    #[inline]
    #[must_use]
    pub fn new<S: AsRef<[u8]> + ?Sized>(slice: &S) -> &Self {
        Self::with_offset(0, slice)
    }

    /// Create a mutable bit slice from a slice.
    ///
    /// # Example
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::from_mut(&mut [0b10101010]);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_mut<S: AsMut<[u8]> + ?Sized>(slice: &mut S) -> &mut Self {
        let slice = slice.as_mut();

        // SAFETY: all args are checked before
        unsafe { Self::from_raw_mut(0, slice.len() * 8, slice.as_mut_ptr()) }
    }

    /// Create a bit slice from a slice with a custom offset on the first byte.
    ///
    /// # Example
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::with_offset(2, &[0b10101010]);
    /// //                                        ^ for the BitSlice the first bit is now here
    /// ```
    #[inline]
    #[must_use]
    pub fn with_offset<S: AsRef<[u8]> + ?Sized>(bit_offset: u8, slice: &S) -> &Self {
        let slice = slice.as_ref();

        Self::with_size_and_offset(
            bit_offset,
            // we need to do - bit_offset to avoid to leave the base slice
            slice.len() * 8 - bit_offset as usize,
            slice,
        )
    }

    /// Create a bit slice from a slice with a custom size.
    ///
    /// # Example
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::with_size(4, &[0b10101010]);
    /// //                                        ^ for the BitSlice the last bit of the slice is here
    /// ```
    #[inline]
    #[must_use]
    pub fn with_size<S: AsRef<[u8]> + ?Sized>(size: usize, slice: &S) -> &Self {
        Self::with_size_and_offset(0, size, slice)
    }

    /// Create a bit slice from a slice with a custom size and offet.
    /// Refer to [`Self::with_size`] and [`Self::with_offset`] to understand
    /// the meaning of size and offset.
    #[inline]
    #[must_use]
    pub fn with_size_and_offset<S: AsRef<[u8]> + ?Sized>(
        bit_offset: u8,
        size: usize,
        slice: &S,
    ) -> &Self {
        let slice = slice.as_ref();

        debug_assert!(bit_offset < 8 && size + bit_offset as usize <= slice.len() * 8);

        // SAFETY: all args are checked before
        unsafe { Self::from_raw(bit_offset, size, slice.as_ptr()) }
    }

    /// Create an immutable bit slice from a pointer to the "first byte" with a
    /// custom size and offet.
    /// Refer to [`Self::with_size`] and [`Self::with_offset`] to understand
    /// the meaning of size and offset.
    ///
    /// # Safety
    /// When the method is called, the pointer must not be a dangling pointer.
    #[inline]
    #[must_use]
    pub unsafe fn from_raw<'s>(bit_offset: u8, size: usize, ptr: *const u8) -> &'s Self {
        from_raw_parts(ptr, size as half_usize, bit_offset)
    }

    /// Create a mutable bit slice from a pointer to the "first byte" with a custom
    /// size and offet.
    /// Refer to [`Self::with_size`] and [`Self::with_offset`] to understand
    /// the meaning of size and offset.
    ///
    /// # Safety
    /// When the method is called, the pointer must not be a dangling pointer.
    #[inline]
    #[must_use]
    pub unsafe fn from_raw_mut<'s>(bit_offset: u8, size: usize, ptr: *mut u8) -> &'s mut Self {
        from_raw_parts_mut(ptr, size as half_usize, bit_offset)
    }

    /// Returns the metadata of the bit slice.
    #[inline]
    #[must_use]
    pub(crate) const fn metadata(&self) -> Metadata {
        ptr_meta::metadata(self)
    }

    /// Returns the start offset, i.e. the shift who bind for example the 3rd
    /// bit to the index 0.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> u8 {
        self.metadata().bit_offset
    }

    /// Returns the number of bits handled by the slice
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.metadata().size as usize
    }

    /// Returns the number of bytes use byte the slice.
    ///
    /// # Note
    ///
    /// The number of bits given by [`len`] can be `N` bytes, but the function can
    /// return `N + 1` or `N + 2`. To understand this, you need to take into account
    /// the notion of slice offset. (explain here [`offset`])
    #[inline]
    #[must_use]
    pub const fn byte_len(&self) -> usize {
        minimal_bytes_size(self.len() + self.offset() as usize)
    }

    /// Check is the slice is empty.
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the first bit of the slice, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b10101010, 0b00000000]);
    /// assert_eq!(bits.first_bit(), Some(true))
    /// ```
    #[inline]
    #[must_use]
    pub const fn first_bit(&self) -> Option<bool> {
        match self.is_empty() {
            false => Some((self.0[0] & (1 << (7 - self.offset()))) != 0),
            true => None,
        }
    }

    /// Returns the first byte of the slice, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b10101010, 0b00000000]);
    /// assert_eq!(bits.first_byte(), Some(0b10101010))
    /// ```
    #[inline]
    #[must_use]
    pub const fn first_byte(&self) -> Option<u8> {
        match self.is_empty() {
            false => Some(self.0[0]),
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
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        &self.0 as *const [u8] as *const u8
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
    /// assert_eq!(bits.get_slice(), &[0b00101000, 0b11011111]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn get_slice(&self) -> &[u8] {
        // SAFETY: the resulting pointer can only a dangling pointer if the pointer
        // get with the method is a dangling pointer itself.
        unsafe { &*core::ptr::slice_from_raw_parts(self.as_ptr(), self.byte_len()) }
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
    #[must_use]
    pub fn get<'s, I: SliceIndex<&'s Self>>(&'s self, index: I) -> Option<I::Output> {
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
    /// # Safety
    /// When the method is called, the index need to be between
    /// `0 <= index < slice.len()`.
    ///
    /// Or if it's a range, the bounds need to respect the previous condition
    /// and the start need to be <= to the end.
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
    /// unsafe { bits.get_unchecked(2..1) };
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked<'s, I: SliceIndex<&'s Self>>(&'s self, index: I) -> I::Output {
        index.get_unchecked(self)
    }

    /// Returns the `index` bytes, if it's in bounts, otherwise it panics.
    ///
    /// # Safety
    /// When the method is called, the index need to be between
    /// `0 <= index < slice.byte_len()`.
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
    #[inline]
    #[must_use]
    pub unsafe fn get_byte_unchecked(&self, index: usize) -> u8 {
        assert!(
            index < self.byte_len(),
            "BitSlice::get_byte_unchecked requires that the index is within the slice"
        );

        self.0[index]
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
    #[inline]
    #[must_use]
    pub fn get_byte(&self, index: usize) -> Option<u8> {
        (index < self.byte_len()).then(|| unsafe { self.get_byte_unchecked(index) })
    }
}

impl<'s> From<&'s [u8]> for &'s BitSlice {
    #[inline]
    fn from(slice: &'s [u8]) -> Self {
        BitSlice::new(slice)
    }
}

impl<'s> From<&'s mut [u8]> for &'s mut BitSlice {
    #[inline]
    fn from(slice: &'s mut [u8]) -> Self {
        BitSlice::from_mut(slice)
    }
}

impl<'s> IntoIterator for &'s BitSlice {
    type IntoIter = super::Iter<'s>;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        super::Iter {
            slice: self,
            index: 0,
        }
    }
}

impl PartialEq<BitSlice> for BitSlice {
    fn eq(&self, other: &BitSlice) -> bool {
        if self.len() != other.len() {
            return false;
        }

        // seem to look like "a == a"
        if self.offset() == other.offset() && self.as_ptr() == other.as_ptr() {
            return true;
        }

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

impl Eq for BitSlice {}

impl fmt::Debug for BitSlice {
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

/// Creates a `&BitSlice` from a pointer and a length and an offset.
///
/// This function is the `BitSlice` equivalent of [`core::slice::from_raw_parts`].
///
/// # Safety
/// See the safety concerns and examples of [`core::slice::from_raw_parts`].
///
/// The mutable version of this function is [`from_raw_parts_mut`].
#[inline]
#[must_use]
pub unsafe fn from_raw_parts<'s>(ptr: *const u8, len: half_usize, offset: u8) -> &'s BitSlice {
    // SAFETY: the caller must uphold the safety contract for `from_raw_parts`.
    unsafe {
        &*ptr_meta::from_raw_parts(
            ptr as _,
            Metadata {
                size: len,
                bit_offset: offset,
            },
        )
    }
}

/// Creates a `&mut BitSlice` from a pointer and a length and an offset.
///
/// This function is the `BitSlice` equivalent of [`core::slice::from_raw_parts_mut`].
///
/// # Safety
/// See the safety concerns and examples of [`core::slice::from_raw_parts_mut`].
///
/// The immutable version of this function is [`from_raw_parts`].
#[inline]
#[must_use]
pub unsafe fn from_raw_parts_mut<'s>(
    ptr: *mut u8,
    len: half_usize,
    offset: u8,
) -> &'s mut BitSlice {
    // SAFETY: the caller must uphold the safety contract for `from_raw_parts_mut`.
    unsafe {
        &mut *ptr_meta::from_raw_parts_mut::<BitSlice>(
            ptr as _,
            Metadata {
                size: len,
                bit_offset: offset,
            },
        )
    }
}

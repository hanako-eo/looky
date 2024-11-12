use core::{cmp::min, fmt, mem::MaybeUninit};

use crate::slice::SliceIndex;
use crate::utils::minimal_bytes_size;

use super::{
    iter::{Iter, IterMut},
    metadata::{half_usize, Metadata},
};

/// BitSlice works like a fat pointer, it describes a byte slice (perhaps seen
/// as equivalent to a `&[u8]`) but its purpose is to allow bit-by-bit manipulation
/// of the array.
pub struct BitSlice(pub(crate) [u8]);

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
        Self::with_offset_mut(0, slice)
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

    /// Create a mutable bit slice from a slice with a custom offset on the first byte.
    ///
    /// # Example
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::with_offset_mut(2, &mut [0b10101010]);
    /// //                                                ^ for the BitSlice the first bit is now here
    /// ```
    #[inline]
    #[must_use]
    pub fn with_offset_mut<S: AsMut<[u8]> + ?Sized>(bit_offset: u8, slice: &mut S) -> &mut Self {
        let slice = slice.as_mut();

        Self::with_size_and_offset_mut(
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

    /// Create a bit mutable slice from a slice with a custom size.
    ///
    /// # Example
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::with_size_mut(4, &mut [0b10101010]);
    /// //                                                ^ for the BitSlice the last bit of the slice is here
    /// ```
    #[inline]
    #[must_use]
    pub fn with_size_mut<S: AsMut<[u8]> + ?Sized>(size: usize, slice: &mut S) -> &mut Self {
        Self::with_size_and_offset_mut(0, size, slice)
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
        unsafe { Self::from_raw(slice.as_ptr(), size, bit_offset) }
    }

    /// Create a mutable bit slice from a slice with a custom size and offet.
    /// Refer to [`Self::with_size_mut`] and [`Self::with_offset_mut`] to understand
    /// the meaning of size and offset.
    #[inline]
    #[must_use]
    pub fn with_size_and_offset_mut<S: AsMut<[u8]> + ?Sized>(
        bit_offset: u8,
        size: usize,
        slice: &mut S,
    ) -> &mut Self {
        let slice = slice.as_mut();

        debug_assert!(bit_offset < 8 && size + bit_offset as usize <= slice.len() * 8);

        // SAFETY: all args are checked before
        unsafe { Self::from_raw_mut(slice.as_mut_ptr(), size, bit_offset) }
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
    pub const unsafe fn from_raw<'s>(ptr: *const u8, size: usize, bit_offset: u8) -> &'s Self {
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
    pub unsafe fn from_raw_mut<'s>(ptr: *mut u8, size: usize, bit_offset: u8) -> &'s mut Self {
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

    /// Returns the number of bytes use by the slice.
    ///
    /// # Note
    ///
    /// The number of bits given by [`len`] can be `N` bytes, but the function can
    /// return `N + 1`. To understand this, you need to take into account
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
    #[inline(always)]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        &self.0 as *const [u8] as *const u8
    }

    /// Returns an unsafe mutable pointer to the slice's buffer.
    ///
    /// The caller must ensure that the slice outlives the pointer this
    /// function returns, or else it will end up dangling.
    ///
    /// Modifying the container referenced by this slice may cause its buffer
    /// to be reallocated, which would also make any pointers to it invalid.
    #[inline(always)]
    #[must_use]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        &mut self.0 as *mut [u8] as *mut u8
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
    /// use looky::bits::{Bit, BitSlice};
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^ this bit
    /// assert_eq!(bits.get(2).map(|b| b.value()), Some(true));
    ///
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^^^^ this range of bits
    /// assert_eq!(bits.get(2..6), Some(BitSlice::with_size_and_offset(2, 4, &[0b00_1010_00])));
    /// //                                                                    retrieve here ^^^^
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

    /// Returns a mutable reference to a bit or subslice depending on the
    /// type of index (see [`get`]) or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::{BitSlice, MutableBit};
    ///
    /// let mut base = [0b00101000, 0b11011111];
    /// let bits = BitSlice::from_mut(&mut base);
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^ this bit
    /// assert_eq!(bits.get_mut(2).map(|b| b.value()), Some(true));
    ///
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^^^^ this range of bits
    /// assert_eq!(bits.get_mut(2..6), Some(BitSlice::with_size_and_offset_mut(2, 4, &mut [0b00_1010_00])));
    /// //                                                                        retrieve here ^^^^
    /// ```
    #[inline]
    #[must_use]
    pub fn get_mut<'s, I: SliceIndex<&'s mut Self>>(&'s mut self, index: I) -> Option<I::Output> {
        index.get(self)
    }

    /// Returns a mutable reference to a bit or subslice depending on the
    /// (see [`get`]).
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
    /// let mut base = [0b00101000, 0b11011111];
    /// let bits = BitSlice::from_mut(&mut base);
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^ this bit
    /// assert_eq!(unsafe { bits.get_mut_unchecked(2) }, true);
    ///
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^^^^ this range of bits
    /// assert_eq!(unsafe { bits.get_mut_unchecked(2..6) }, BitSlice::with_size_and_offset_mut(2, 4, &mut [0b00_1010_00]));
    /// //                                                                                        retrieve here ^^^^
    /// ```
    ///
    /// ```should_panic
    /// use looky::bits::BitSlice;
    ///
    /// let mut base = [0b00101000, 0b11011111];
    /// let bits = BitSlice::from_mut(&mut base);
    ///
    /// unsafe { bits.get_mut_unchecked(20..60) };
    /// unsafe { bits.get_mut_unchecked(2..1) };
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn get_mut_unchecked<'s, I: SliceIndex<&'s mut Self>>(
        &'s mut self,
        index: I,
    ) -> I::Output {
        index.get_unchecked(self)
    }

    /// Returns the `index` bytes, if it's out of bounts, it will return `None`.
    ///
    /// If the byte cannot be obtained simply from the original slice, it will
    /// try to construct it like normal numbers.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::BitSlice;
    ///
    /// let bits = BitSlice::new(&[0b00101000, 0b11011111]);
    ///
    /// // try to get the second byte
    /// assert_eq!(bits.get_byte(0), Some(0b00101000));
    /// assert_eq!(bits.get_byte(1), Some(0b11011111));
    ///
    /// // the new slice will start from the first 1 in '0b00*1*01000'
    /// let bits2 = bits.shift(2);
    ///
    /// assert_eq!(bits2.get_byte(0), Some(0b10100011));
    /// assert_eq!(bits2.get_byte(1), Some(0b00011111));
    /// //                                     ^^^^^^ reconstruct part
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

    /// Returns the `index` bytes, if it's in bounts, otherwise it panics.
    ///
    /// If the byte cannot be obtained simply from the original slice, it will
    /// try to construct it like normal numbers.
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
    /// assert_eq!(unsafe { bits.get_byte_unchecked(0) }, 0b00101000);
    /// // try to get the second byte
    /// assert_eq!(unsafe { bits.get_byte_unchecked(1) }, 0b11011111);
    ///
    /// // the new slice will start from the first 1 in '0b00*1*01000'
    /// let bits2 = bits.shift(2);
    ///
    /// assert_eq!(unsafe { bits2.get_byte_unchecked(0) }, 0b10100011);
    /// assert_eq!(unsafe { bits2.get_byte_unchecked(1) }, 0b00011111);
    /// //                                                     ^^^^^^ reconstruct part
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
    pub unsafe fn get_byte_unchecked(&self, index: usize) -> u8 {
        assert!(
            index * 8 < self.len(),
            "BitSlice::get_byte_unchecked requires that the index is within the slice"
        );

        // check if the slice has no bit offset or if it's the last byte check it has at least 8 bits
        if self.offset() == 0 && self.len() - index * 8 > 7 {
            return self.0[index];
        }

        let start = index * 8;
        let end = min(start + 8, self.len());

        (start..end)
            .map(|i| self.get_unchecked(i))
            .fold(0, |acc, bit| acc << 1 | bit.value() as u8)
    }

    /// Perform a shift left of the slice and reduce the len of the slice by the
    /// same amount of the shift to avoid undefined behavior.
    pub fn shift(&self, shift: usize) -> &Self {
        assert!(
            shift < self.len(),
            "BitSlice::shift requires that the shift is within the slice"
        );

        unsafe { self.get_unchecked(shift..) }
    }

    /// Divides one slice into two at an index, returning `None` if the slice is
    /// too short.
    ///
    /// If `mid ≤ len` returns a pair of slices where the first will contain all
    /// indices from `[0, mid)` (excluding the index `mid` itself) and the
    /// second will contain all indices from `[mid, len)` (excluding the index
    /// `len` itself).
    ///
    /// Otherwise, if `mid > len`, returns `None`.
    #[inline]
    #[must_use]
    pub fn split_n_time<const N: usize>(&self, size: usize) -> Option<([&Self; N], &Self)> {
        let mut array = MaybeUninit::<[&Self; N]>::uninit();
        let ptr = array.as_mut_ptr() as *mut &Self;
        let mut slice = self;

        for i in 0..N {
            let chunk;
            (chunk, slice) = slice.split_at(size)?;
            // SAFETY: `i` will not exceed N
            unsafe {
                ptr.add(i).write(chunk);
            }
        }

        // SAFETY: correctly init before
        Some((unsafe { array.assume_init() }, slice))
    }

    /// Divides one slice into two at an index, returning `None` if the slice is
    /// too short.
    ///
    /// If `mid ≤ len` returns a pair of slices where the first will contain all
    /// indices from `[0, mid)` (excluding the index `mid` itself) and the
    /// second will contain all indices from `[mid, len)` (excluding the index
    /// `len` itself).
    ///
    /// Otherwise, if `mid > len`, returns `None`.
    #[inline]
    #[must_use]
    pub fn split_at(&self, mid: usize) -> Option<(&Self, &Self)> {
        (mid <= self.len()).then(|| unsafe { self.split_at_unchecked(mid) })
    }

    /// Divides one slice into two at an index, without doing bounds checking.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// For a safe alternative see [`split_at`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used. The caller has to ensure that
    /// `0 <= mid <= self.len()`.
    ///
    /// [`split_at`]: slice::split_at
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use]
    pub unsafe fn split_at_unchecked(&self, mid: usize) -> (&Self, &Self) {
        let len = self.len();
        assert!(
            mid <= len,
            "BitSlice::split_at_unchecked requires the index to be within the slice (max {len})",
        );

        (self.get_unchecked(..mid), self.get_unchecked(mid..))
    }

    /// Divides one mutable slice into two at an index, returning `None` if the
    /// slice is too short.
    ///
    /// If `mid ≤ len` returns a pair of slices where the first will contain all
    /// indices from `[0, mid)` (excluding the index `mid` itself) and the
    /// second will contain all indices from `[mid, len)` (excluding the index
    /// `len` itself).
    ///
    /// Otherwise, if `mid > len`, returns `None`.
    #[inline]
    #[must_use]
    pub fn split_at_mut(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
        (mid <= self.len()).then(|| unsafe { self.split_at_mut_unchecked(mid) })
    }

    /// Divides one mutable slice into two at an index, without doing bounds checking.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// For a safe alternative see [`split_at_mut`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used. The caller has to ensure that
    /// `0 <= mid <= self.len()`.
    ///
    /// [`split_at_mut`]: slice::split_at_mut
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use]
    pub unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        let len = self.len();
        assert!(
            mid <= len,
            "BitSlice::split_at_mut_unchecked requires the index to be within the slice (max {len})",
        );

        let ptr = self.as_mut_ptr();

        let slice_offset = self.offset() as usize;
        let rest_size = len.unchecked_sub(mid);
        let mid = mid + slice_offset;

        let offset_bits = (mid % 8) as u8;
        let offset_byte = mid / 8;

        // We use `from_raw_mut` instead of `get_mut_unchecked` to avoid error
        // 'cannot borrow `*self` as mutable more than once at a time'
        (
            Self::from_raw_mut(ptr, mid, self.offset()),
            Self::from_raw_mut(ptr.add(offset_byte), rest_size, offset_bits),
        )
    }

    /// Returns an iterator over the slice.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }

    /// Returns an iterator that allows modifying each bits.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        IterMut::new(self)
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
    type IntoIter = Iter<'s>;
    type Item = <Self::IntoIter as Iterator>::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
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
        let mut it = self.into_iter().enumerate();

        match it.next() {
            None => return write!(f, "0b0"),
            Some((_, bit)) => write!(f, "0b{bit}")?,
        }

        for (i, bit) in it {
            if i % 8 == 0 {
                write!(f, "_{bit}")?;
            } else {
                write!(f, "{bit}")?;
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
pub const unsafe fn from_raw_parts<'s>(
    ptr: *const u8,
    len: half_usize,
    offset: u8,
) -> &'s BitSlice {
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

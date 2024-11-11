use core::ops::{Bound, RangeBounds};

use crate::bits::{Bit, BitSlice, MutableBit};
use crate::marker::RangeMarker;

pub trait SliceIndex<T: ?Sized> {
    /// The output type returned by methods.
    type Output: Sized;

    /// Returns the output at this location, if in bounds.
    fn get(self, slice: T) -> Option<Self::Output>;

    /// Returns the output at this location, can panicking if out of bounds.
    unsafe fn get_unchecked(self, slice: T) -> Self::Output;
}

impl<'s> SliceIndex<&'s BitSlice> for usize {
    type Output = Bit;

    /// Returns a bool at this location, if in bounds.
    /// In the case of the locatiohn is out of bounds, it returns `None`.
    #[inline]
    fn get(self, slice: &'s BitSlice) -> Option<Self::Output> {
        // SAFETY: self it's in the bounds
        (self < slice.len()).then(|| unsafe { self.get_unchecked(slice) })
    }

    /// Returns the output at this location, it panic if it's out of bounds.
    #[inline]
    unsafe fn get_unchecked(self, slice: &'s BitSlice) -> Self::Output {
        assert!(
            self < slice.len(),
            "<usize as SliceIndex<BitSlice>>::get_unchecked requires that the index is within the slice"
        );

        let index = self + slice.offset() as usize;
        Bit::new(&slice.0[index / 8], (index % 8) as u8)
    }
}

// To understand the whys ans wherefors of the '+ RangeMarker' go to the
// definition of RangeMarker.
impl<'s, R: RangeBounds<usize> + RangeMarker> SliceIndex<&'s BitSlice> for R {
    type Output = &'s BitSlice;

    /// Retrieves the self-th bit.
    #[inline]
    fn get(self, slice: &'s BitSlice) -> Option<Self::Output> {
        let start = match self.start_bound() {
            Bound::Included(index) => *index,
            Bound::Excluded(index) => index + 1,
            Bound::Unbounded => 0,
        };

        let end = match self.end_bound() {
            Bound::Included(index) => index + 1,
            Bound::Excluded(index) => *index,
            Bound::Unbounded => slice.len(),
        };

        if start > end {
            return None;
        }

        (end <= slice.len()).then(|| unsafe { self.get_unchecked(slice) })
    }

    /// Retrieves the reference to the byte containing the self-th bit.
    unsafe fn get_unchecked(self, slice: &'s BitSlice) -> Self::Output {
        let start = match self.start_bound() {
            Bound::Included(index) => *index,
            Bound::Excluded(index) => index + 1,
            Bound::Unbounded => 0,
        };

        let end = match self.end_bound() {
            Bound::Included(index) => index + 1,
            Bound::Excluded(index) => *index,
            Bound::Unbounded => slice.len(),
        };

        assert!(
            start < slice.len(),
            "range start index {start} out of range for slice of length {}",
            slice.len()
        );
        assert!(
            end <= slice.len(),
            "range end index {end} out of range for slice of length {}",
            slice.len()
        );
        assert!(
            start <= end,
            "slice index starts at {start} but ends at {end}"
        );

        let slice_offset = slice.offset() as usize;
        let size = end - start + slice_offset;

        let start = start + slice_offset;

        let offset_bits = (start % 8) as u8;
        let offset_byte = start / 8;

        BitSlice::from_raw(slice.as_ptr().add(offset_byte), size, offset_bits)
    }
}

impl<'s> SliceIndex<&'s mut BitSlice> for usize {
    type Output = MutableBit;

    /// Returns a bool at this location, if in bounds.
    /// In the case of the locatiohn is out of bounds, it returns `None`.
    #[inline]
    fn get(self, slice: &'s mut BitSlice) -> Option<Self::Output> {
        // SAFETY: self it's in the bounds
        (self < slice.len()).then(|| unsafe { self.get_unchecked(slice) })
    }

    /// Returns the output at this location, it panic if it's out of bounds.
    #[inline]
    unsafe fn get_unchecked(self, slice: &'s mut BitSlice) -> Self::Output {
        assert!(
            self < slice.len(),
            "<usize as SliceIndex<BitSlice>>::get_unchecked requires that the index is within the slice"
        );

        let index = self + slice.offset() as usize;
        MutableBit::new(&mut slice.0[index / 8], (index % 8) as u8)
    }
}

// To understand the whys ans wherefors of the '+ RangeMarker' go to the
// definition of RangeMarker.
impl<'s, R: RangeBounds<usize> + RangeMarker> SliceIndex<&'s mut BitSlice> for R {
    type Output = &'s mut BitSlice;

    /// Retrieves the self-th bit.
    #[inline]
    fn get(self, slice: &'s mut BitSlice) -> Option<Self::Output> {
        let start = match self.start_bound() {
            Bound::Included(index) => *index,
            Bound::Excluded(index) => index + 1,
            Bound::Unbounded => 0,
        };

        let end = match self.end_bound() {
            Bound::Included(index) => index + 1,
            Bound::Excluded(index) => *index,
            Bound::Unbounded => slice.len(),
        };

        if start > end {
            return None;
        }

        (end <= slice.len()).then(|| unsafe { self.get_unchecked(slice) })
    }

    /// Retrieves the reference to the byte containing the self-th bit.
    unsafe fn get_unchecked(self, slice: &'s mut BitSlice) -> Self::Output {
        let start = match self.start_bound() {
            Bound::Included(index) => *index,
            Bound::Excluded(index) => index + 1,
            Bound::Unbounded => 0,
        };

        let end = match self.end_bound() {
            Bound::Included(index) => index + 1,
            Bound::Excluded(index) => *index,
            Bound::Unbounded => slice.len(),
        };

        assert!(
            start < slice.len(),
            "range start index {start} out of range for slice of length {}",
            slice.len()
        );
        assert!(
            end <= slice.len(),
            "range end index {end} out of range for slice of length {}",
            slice.len()
        );
        assert!(
            start <= end,
            "slice index starts at {start} but ends at {end}"
        );

        let slice_offset = slice.offset() as usize;
        let size = end - start + slice_offset;

        let start = start + slice_offset;

        let offset_bits = (start % 8) as u8;
        let offset_byte = start / 8;

        BitSlice::from_raw_mut(slice.as_mut_ptr().add(offset_byte), size, offset_bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_correctly_the_n_th_bit() {
        let bits = BitSlice::new(&[0b00100000, 0b11011111]);

        assert_eq!(bits.get(2).map(Bit::value), Some(true));
        assert_eq!(bits.get(10).map(Bit::value), Some(false));

        assert_ne!(bits.get(1).map(Bit::value), Some(true));
        assert_eq!(bits.get(20), None);
    }

    #[test]
    fn get_correctly_a_range_of_bytes() {
        let bits = BitSlice::new(&[0b00100000, 0b11011111]);

        assert_eq!(bits.get(0..16), Some(bits));
        assert_eq!(bits.get(0..=15), Some(bits));
        assert_eq!(bits.get(0..), Some(bits));
        assert_eq!(bits.get(..), Some(bits));
        assert_eq!(bits.get(..=15), Some(bits));
        assert_eq!(bits.get(..16), Some(bits));

        assert_eq!(
            bits.get(2..4),
            Some(BitSlice::with_size_and_offset(2, 2, &[0b00_10_0000]))
        );
        assert_eq!(
            bits.get(2..10),
            Some(BitSlice::with_size_and_offset(
                2,
                8,
                &[0b00_100000, 0b11_100000]
            ))
        );
        assert_eq!(
            bits.get(2..12),
            Some(BitSlice::with_size_and_offset(
                2,
                10,
                &[0b00_100000, 0b1101_0000]
            ))
        );
        assert_eq!(bits.get(2..20), None);
        assert_eq!(bits.get(20..), None);
        assert_eq!(bits.get(..20), None);
    }
}

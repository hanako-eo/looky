use core::ops::{Bound, RangeBounds};

use private_marker::RangeMarker;

use crate::bits::Bits;

pub trait SliceIndex<T: ?Sized> {
    /// The output type returned by methods.
    type Output: Sized;

    /// Returns a shared reference to the output at this location, if in
    /// bounds.
    fn get(self, slice: &T) -> Option<Self::Output>;

    /// Returns a shared reference to the output at this location, panicking
    /// if out of bounds.
    fn index(self, slice: &T) -> Self::Output;
}

impl SliceIndex<Bits> for usize {
    type Output = u8;

    /// Retrieves the self-th bit.
    #[inline]
    fn get(self, slice: &Bits) -> Option<Self::Output> {
        (self < slice.len()).then(|| (self.index(slice) & (1 << 7 - self % 8)) >> 7 - self % 8)
    }

    /// Retrieves the byte containing the self-th bit.
    #[inline]
    fn index(self, slice: &Bits) -> Self::Output {
        slice.0[self / 8]
    }
}

#[inline]
const fn minimal_bytes_size(bits: usize) -> usize {
    bits / 8 + (bits % 8 > 0) as usize
}

// To understand the whys ans wherefors of the '+ RangeMarker' go to the
// definition of RangeMarker.
impl<R: RangeBounds<usize> + RangeMarker> SliceIndex<Bits> for R {
    // We need to allocate the memory in the Box because we cannot know in advance
    // the size of the range, and furthermore for now we cannot pre-alloc at the
    // compile time because `feature(generic_const_exprs)` is unstable in 1.82.
    type Output = Box<Bits>;

    /// Retrieves the self-th bit.
    #[inline]
    fn get(self, slice: &Bits) -> Option<Self::Output> {
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

        if start >= end {
            // no need to allocate anything
            return None;
        }

        (end <= slice.len()).then(|| self.index(slice))
    }

    /// Retrieves the reference to the byte containing the self-th bit.
    fn index(self, slice: &Bits) -> Self::Output {
        // This function calculates an array of bits and copies the slice into
        // the self interval, doing something like this:
        // 00000000_0000|0000_00000000_0000|0000_00000000 complete sequence
        //               ^----------------^ <- range

        let start = match self.start_bound() {
            Bound::Included(index) => *index,
            Bound::Excluded(index) => index + 1,
            Bound::Unbounded => 0,
        };

        let end = match self.end_bound() {
            Bound::Included(index) => *index,
            Bound::Excluded(index) => index - 1,
            Bound::Unbounded => slice.len() - 1,
        };

        if start >= end {
            return Bits::new_box(&[]);
        }

        let bytes_size = minimal_bytes_size(end - start);

        // Create the array of bytes (init to 0)
        let mut bits = {
            let mut bits = Box::<[u8]>::new_uninit_slice(bytes_size);
            for i in 0..bytes_size {
                bits[i].write(0);
            }
            unsafe { bits.assume_init() }
        };

        // Set the n-th bit of the slice to the m-th bit of the array (`bits`)
        for i in start..=end {
            let offset = i - start;
            // (i % 8) is the shit from 0b10...0 to 0b1 of the bit in the slice
            // (offset % 8) is the shit from 0b1 to 0b10...0 for the bit in the array
            let shift = (i % 8) as i8 - (offset % 8) as i8;

            let bit = slice.0[i / 8] & 1 << 7 - (i % 8);
            bits[offset / 8] |= if shift.is_negative() {
                bit >> -shift
            } else {
                bit << shift
            }
        }

        bits.into()
    }
}

mod private_marker {
    use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

    /// The existence of this private marker is due to the error:
    /// ```"not rust"
    /// error[E0119]: conflicting implementations of trait `slice::SliceIndex<Bits>` for type `usize`
    ///    = note: upstream crates may add a new impl of trait `std::ops::RangeBounds<usize>` for type `usize` in future versions
    /// ```
    ///
    /// and that thanks to this marker, which will be implemented on the same structure
    /// as RangeBounds (must remain exosive to avoid giving the same error), the error
    /// will disappear.
    ///
    /// <https://stackoverflow.com/questions/39159226/conflicting-implementations-of-trait-in-rust>
    pub trait RangeMarker {}

    impl RangeMarker for Range<usize> {}
    impl RangeMarker for RangeFrom<usize> {}
    impl RangeMarker for RangeTo<usize> {}
    impl RangeMarker for RangeInclusive<usize> {}
    impl RangeMarker for RangeToInclusive<usize> {}
    impl RangeMarker for RangeFull {}
}

mod tests {
    use super::*;

    #[test]
    fn get_correctly_the_n_th_bit() {
        let bits = Bits::new(&[0b00100000, 0b11011111]);

        assert_eq!(bits.get(2), Some(1));
        assert_eq!(bits.get(10), Some(0));

        assert_eq!(bits.get(20), None);
        assert_ne!(bits.get(1), Some(1));
    }

    #[test]
    fn get_correctly_a_range_of_bytes() {
        let bits = Bits::new(&[0b00100000, 0b11011111]);

        assert_eq!(bits.get(0..16), Some(Box::from(bits)));
        assert_eq!(bits.get(0..=15), Some(Box::from(bits)));
        assert_eq!(bits.get(0..), Some(Box::from(bits)));

        assert_eq!(bits.get(2..4), Some(Box::from(Bits::new(&[0b10000000]))));
        assert_eq!(bits.get(2..10), Some(Box::from(Bits::new(&[0b10000011]))));
        assert_eq!(
            bits.get(2..12),
            Some(Box::from(Bits::new(&[0b10000011, 0b01000000])))
        );
        assert_eq!(bits.get(2..20), None);
        assert_eq!(bits.get(20..), None);
    }
}

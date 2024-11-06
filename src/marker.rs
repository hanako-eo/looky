use core::ops::{Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

/// The existence of this private marker is due to the error:
/// ```"not rust"
/// error[E0119]: conflicting implementations of trait `slice::SliceIndex<BitSlice>` for type `usize`
///    = note: upstream crates may add a new impl of trait `std::ops::RangeBounds<usize>` for type `usize` in future versions
/// ```
///
/// and that thanks to this marker, which will be implemented on the same structure
/// as RangeBounds (must remain exosive to avoid giving the same error), the error
/// will disappear.
///
/// <https://stackoverflow.com/questions/39159226/conflicting-implementations-of-trait-in-rust>
pub(crate) trait RangeMarker {}

impl RangeMarker for Range<usize> {}
impl RangeMarker for RangeFrom<usize> {}
impl RangeMarker for RangeTo<usize> {}
impl RangeMarker for RangeInclusive<usize> {}
impl RangeMarker for RangeToInclusive<usize> {}
impl RangeMarker for RangeFull {}
impl RangeMarker for (Bound<usize>, Bound<usize>) {}

#![allow(non_camel_case_types)]

use ptr_meta::Pointee;
use static_assertions::assert_eq_size;

use super::BitSlice;

#[cfg(target_pointer_width = "64")]
pub type half_usize = u32;

#[cfg(target_pointer_width = "32")]
pub type half_usize = u16;

#[cfg(target_pointer_width = "16")]
pub type half_usize = u8;

/// Metadata of the BitSlice.
///
/// The structure definition can see I strange, why we need a [`half_usize`] ?
/// That's because it's not possible to create your own [`Pointee`], the size of
/// our structure need to feet the size of a usize.
///
/// It's due to the fact that `[u8]` is a [DST] and in memory the reference is
/// like a tuple of a pointer and the length (`&[T]` is a fat pointer) and since
/// length is a `usize`, we take the haft of the usize to store the real length
/// and the rest for the offset.
/// So in other words `size_of::<usize>() / 2` bytes are dedicated for the length
/// and 1 for the offset.
///
/// [DST]: https://doc.rust-lang.org/reference/dynamically-sized-types.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Metadata {
    pub(crate) size: half_usize,
    pub(crate) bit_offset: u8,
}

assert_eq_size!(Metadata, usize);

unsafe impl Send for Metadata {}
unsafe impl Sync for Metadata {}
impl Unpin for Metadata {}

unsafe impl Pointee for BitSlice {
    type Metadata = Metadata;
}

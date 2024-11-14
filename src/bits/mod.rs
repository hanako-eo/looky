//! This module contains all the structures and various objects that can be
//! manipulated bit by bit or related to this type of object.

pub use bit::*;
pub use fixed::BitArray;
pub use slice::*;
#[cfg(feature = "alloc")]
pub use vec::*;

mod bit;
mod fixed;
mod iter;
mod metadata;
mod slice;
#[cfg(feature = "alloc")]
mod vec;

pub mod error {
    pub struct CopyError;
}

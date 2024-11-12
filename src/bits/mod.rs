//! This module contains all the structures and various objects that can be
//! manipulated bit by bit or related to this type of object.

pub use bit::*;
pub use fixed::BitArray;
pub use slice::*;

mod bit;
mod fixed;
mod iter;
mod metadata;
mod slice;

pub mod error {
    pub struct CopyError;
}

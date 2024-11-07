//! This module contains all the structures and various objects that can be
//! manipulated bit by bit or related to this type of object.

pub use fixed::BitArray;
pub use iter::Iter;
pub use slice::*;

mod fixed;
mod iter;
mod metadata;
mod slice;

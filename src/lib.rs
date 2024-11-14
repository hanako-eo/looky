#![doc = include_str!("../README.md")]
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod bits;
pub mod buffer;
pub mod decode;
mod marker;
mod slice;
mod utils;

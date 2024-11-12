use core::marker::PhantomData;

use super::{Bit, BitSlice, MutableBit};

pub struct Iter<'s> {
    slice: &'s BitSlice,
    index: usize,
}

impl<'s> Iter<'s> {
    pub fn new(slice: &'s BitSlice) -> Self {
        Self { slice, index: 0 }
    }
}

impl<'s> Iterator for Iter<'s> {
    type Item = Bit<'s>;

    // TODO: try to improuve it a little bit ?
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.slice.get(self.index);
        if item.is_some() {
            self.index += 1;
        }
        item
    }
}

pub struct IterMut<'s> {
    // TODO: remove the ptr by a mutable ref
    slice: *mut BitSlice,
    index: usize,
    phantom: PhantomData<&'s ()>,
}

impl<'s> IterMut<'s> {
    pub fn new(slice: &'s mut BitSlice) -> Self {
        Self {
            slice,
            index: 0,
            phantom: PhantomData,
        }
    }
}

impl<'s> Iterator for IterMut<'s> {
    type Item = MutableBit<'s>;

    // TODO: try to improuve it a little bit ?
    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: self.slice will never be null
        let slice = unsafe { self.slice.as_mut().unwrap() };
        let item = slice.get_mut(self.index);
        if item.is_some() {
            self.index += 1;
        }
        item
    }
}

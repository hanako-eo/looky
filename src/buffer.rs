use crate::bits::BitSlice;
use crate::decode::{Decode, DecodeError};

pub struct BitsReader<'s> {
    slice: &'s BitSlice,
}

impl<'s> BitsReader<'s> {
    pub fn new(slice: &'s BitSlice) -> Self {
        Self { slice }
    }

    pub fn read<D: Decode>(&mut self) -> Result<D, DecodeError> {
        let (to_read, slice) = self
            .slice
            .split_at(D::SIZE)
            .ok_or(DecodeError::NotEnoughSpace)?;
        self.slice = slice;

        D::decode(to_read)
    }
}

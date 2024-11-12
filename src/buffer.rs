use crate::bits::BitSlice;
use crate::decode::{Decode, DecodeError};

pub struct BitsReader<'s> {
    slice: &'s BitSlice,
}

impl<'s> BitsReader<'s> {
    pub fn new(slice: &'s BitSlice) -> Self {
        Self { slice }
    }

    pub fn buffer(&self) -> &BitSlice {
        self.slice
    }

    pub fn consume(&mut self, size: usize) -> bool {
        self.pick(size).is_ok()
    }

    pub fn pick(&mut self, size: usize) -> Result<&BitSlice, DecodeError> {
        let (chunk, slice) = self
            .slice
            .split_at(size)
            .ok_or(DecodeError::NotEnoughSpace)?;

        self.slice = slice;

        Ok(chunk)
    }

    pub fn read<D: Decode>(&mut self) -> Result<D, DecodeError> {
        D::decode(self.pick(D::SIZE)?)
    }

    pub fn read_exact_slice(&mut self, result_slice: &mut BitSlice) -> Result<(), DecodeError> {
        let unconsumed_chunk = self.pick(result_slice.len())?;

        result_slice
            .try_copy_from_slice(unconsumed_chunk)
            .map_err(|_| DecodeError::UnmachingSize)
    }
}

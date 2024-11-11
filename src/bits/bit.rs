use core::fmt;

#[derive(Clone, Copy)]
pub struct Bit {
    byte_ptr: *const u8,
    index: u8,
}

impl Bit {
    pub fn new(byte: &u8, index: u8) -> Self {
        Self::from_raw(byte, index)
    }

    pub(crate) fn from_raw(byte_ptr: *const u8, index: u8) -> Self {
        Self { byte_ptr, index }
    }

    pub fn value(self) -> bool {
        unsafe { *self.byte_ptr & (1 << (7 - self.index)) != 0 }
    }
}

impl PartialEq for Bit {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl PartialEq<bool> for Bit {
    fn eq(&self, other: &bool) -> bool {
        self.value() == *other
    }
}

impl fmt::Debug for Bit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

impl fmt::Display for Bit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

#[derive(Clone, Copy)]
pub struct MutableBit {
    byte_ptr: *mut u8,
    index: u8,
}

impl MutableBit {
    pub fn new(byte: &mut u8, index: u8) -> Self {
        Self::from_raw(byte, index)
    }

    pub(crate) fn from_raw(byte_ptr: *mut u8, index: u8) -> Self {
        Self { byte_ptr, index }
    }

    /// Set the bit to 1.
    pub fn set(&mut self) {
        unsafe { *self.byte_ptr |= 1 << (self.index - 1) }
    }
    
    /// Set the bit to 0.
    pub fn reset(&mut self) {
        unsafe { *self.byte_ptr &= !(1 << (self.index - 1)) }
    }
    
    /// Toggle the bit.
    pub fn toggle(&mut self) {
        unsafe { *self.byte_ptr ^= 1 << (self.index - 1) }
    }
    
    /// Get the value of the bit
    pub fn value(self) -> bool {
        unsafe { *self.byte_ptr & (1 << (7 - self.index)) != 0 }
    }
}

impl PartialEq for MutableBit {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl PartialEq<bool> for MutableBit {
    fn eq(&self, other: &bool) -> bool {
        self.value() == *other
    }
}

impl fmt::Debug for MutableBit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

impl fmt::Display for MutableBit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

use core::fmt;

/// Represent a immutable ref of a bit from a ref a byte 
#[derive(Clone, Copy)]
pub struct Bit<'b> {
    byte: &'b u8,
    index: u8,
}

impl<'b> Bit<'b> {
    // Create a ref of a bit from a byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::Bit;
    ///
    /// let n = 1;
    /// let bit = Bit::new(&n, 0);
    ///
    /// assert_eq!(bit.value(), true);
    /// ```
    #[inline]
    #[must_use]
    pub fn new(byte: &'b u8, index: u8) -> Self {
        Self { byte, index }
    }

    /// Get the value of the bit
    #[inline]
    #[must_use]
    pub fn value(&self) -> bool {
        *self.byte & (1 << self.index) != 0
    }
}

impl<'b> PartialEq for Bit<'b> {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl<'b> PartialEq<bool> for Bit<'b> {
    fn eq(&self, other: &bool) -> bool {
        self.value() == *other
    }
}

impl<'b> fmt::Debug for Bit<'b> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

impl<'b> fmt::Display for Bit<'b> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

/// Represent a mutable ref of a bit from a ref a byte
pub struct MutableBit<'b> {
    byte: &'b mut u8,
    index: u8,
}

impl<'b> MutableBit<'b> {
    /// Create a mutable ref of a bit from a mutable byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::MutableBit;
    ///
    /// let mut n = 1;
    /// let mut bit = MutableBit::new(&mut n, 0);
    ///
    /// assert_eq!(bit.value(), true);
    ///
    /// bit.reset();
    /// assert_eq!(bit.value(), false);
    /// //assert_eq!(n, 0);
    ///
    /// bit.set();
    /// assert_eq!(bit.value(), true);
    ///
    /// bit.toggle();
    /// assert_eq!(bit.value(), false);
    /// bit.toggle();
    /// assert_eq!(bit.value(), true);
    /// ```
    #[inline]
    #[must_use]
    pub fn new(byte: &'b mut u8, index: u8) -> Self {
        Self { byte, index }
    }

    /// Set the bit to 1.
    #[inline]
    pub fn set(&mut self) {
        *self.byte |= 1 << self.index
    }

    /// Set the bit to 0.
    #[inline]
    pub fn reset(&mut self) {
        *self.byte &= !(1 << self.index)
    }

    /// Toggle the bit.
    #[inline]
    pub fn toggle(&mut self) {
        *self.byte ^= 1 << self.index
    }

    /// Get the value of the bit
    #[inline]
    #[must_use]
    pub fn value(&self) -> bool {
        *self.byte & (1 << self.index) != 0
    }
}

impl<'b> PartialEq for MutableBit<'b> {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl<'b> PartialEq<bool> for MutableBit<'b> {
    fn eq(&self, other: &bool) -> bool {
        self.value() == *other
    }
}

impl<'b> fmt::Debug for MutableBit<'b> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

impl<'b> fmt::Display for MutableBit<'b> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value() { '1' } else { '0' })
    }
}

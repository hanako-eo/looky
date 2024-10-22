use core::fmt::Debug;
use core::mem::transmute;
use core::ops::{Shl, ShlAssign};

use crate::slice::SliceIndex;

/// Bits is a array of `N*8` bits (store with an normal array, make sure it's
/// the minimum number of bytes you need)
#[derive(PartialEq)]
#[repr(transparent)]
pub struct Bits(pub(crate) [u8]);

impl Bits {
    #[inline]
    pub fn new<S: AsRef<[u8]> + ?Sized>(slice: &S) -> &Self {
        // SAFETY: Bits is just a wrapper around [u8],
        // therefore converting &[u8] to &Bits is safe.
        unsafe { &*(slice.as_ref() as *const [u8] as *const Bits) }
    }
    #[inline]
    pub fn new_box<S: AsRef<[u8]> + Sized>(slice: S) -> Box<Self> {
        Self::into_box(Self::new(&slice))
    }

    #[inline]
    pub fn from_mut<S: AsMut<[u8]> + ?Sized>(slice: &mut S) -> &mut Self {
        // SAFETY: Bits is just a wrapper around [u8],
        // therefore converting &mut [u8] to &mut Bits is safe.
        unsafe { &mut *(slice.as_mut() as *mut [u8] as *mut Bits) }
    }

    #[inline]
    pub fn into_box(bits: &Self) -> Box<Self> {
        // SAFETY: Bits is just a wrapper around [u8],
        // therefore converting &mut [u8] to &mut Bits is safe.
        unsafe { transmute::<Box<[u8]>, Box<Bits>>(Box::from(&bits.0)) }
    }

    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len() * 8
    }

    #[inline]
    #[must_use]
    pub const fn byte_len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[must_use]
    pub const fn first_bit(&self) -> Option<u8> {
        match self.0.first() {
            Some(first) => Some(*first & 0b10000000 >> 7),
            None => None,
        }
    }

    #[inline]
    #[must_use]
    pub const fn first_byte(&self) -> Option<u8> {
        match self.0.first() {
            Some(first) => Some(*first),
            None => None,
        }
    }

    /// This function get the n-th bit of the bits if the index is an integer (`usize`),
    /// otherwise if it's a range it will return an [`Box`] which will contain
    /// the slice of bits request.
    ///
    /// Indexs works "normally", i.e. in the same way as an array, for exemple:
    /// ```"not rust"
    /// 10011100 <- it's at the index 7
    /// ^ it's at the index 0
    /// ```
    ///
    /// ```
    /// use looky::bits::Bits;
    ///
    /// let bits = Bits::new(&[0b00101000, 0b11011111]);
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^ this bit
    /// assert_eq!(bits.get(2), Some(1));
    ///
    /// // try to get [0b00101000, 0b11011111]
    /// //                 ^^^^ this range of bits
    /// assert_eq!(bits.get(2..6), Some(Box::from(Bits::new(&[0b10100000]))));
    /// //                                                      ^^^^ store here
    /// ```
    #[inline]
    pub fn get<I: SliceIndex<Self>>(&self, index: I) -> Option<<I as SliceIndex<Self>>::Output> {
        index.get(self)
    }
}

impl Debug for Bits {
    /// Print in debug mode the bits.
    ///
    /// ```
    /// use looky::bits::Bits;
    ///
    /// let bits = Bits::new(&[0b10011001, 0b01100110, 0b11110000, 0b00001111]);
    ///
    /// assert_eq!(format!("{:?}", bits), String::from("0b10011001_01100110_11110000_00001111"));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut it = self.0.iter();
        match it.next() {
            None => return write!(f, "0b0"),
            Some(byte) => write!(f, "0b{:08b}", byte)?,
        }
        for byte in it {
            write!(f, "_{:08b}", byte)?;
        }
        Ok(())
    }
}

impl Shl<usize> for &Bits {
    type Output = Box<Bits>;

    /// Performs the `<<` operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::Bits;
    ///
    /// let bits = Bits::new(&[0b00001111, 0b11110000]);
    /// assert_eq!(bits << 1, Bits::new_box(&[0b00011111, 0b11100000]));
    /// ```
    fn shl(self, shift: usize) -> Self::Output {
        let mut bits = Bits::into_box(self);
        *bits <<= shift;
        bits
    }
}

impl Shl<usize> for &mut Bits {
    type Output = Box<Bits>;

    /// Performs the `<<` operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::Bits;
    ///
    /// let bits = Bits::new(&[0b00001111, 0b11110000]);
    /// assert_eq!(bits << 1, Bits::new_box(&[0b00011111, 0b11100000]));
    /// ```
    #[inline]
    fn shl(self, shift: usize) -> Self::Output {
        Shl::shl(&*self, shift)
    }
}

impl ShlAssign<usize> for Bits {
    /// Performs the `<<=` operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use looky::bits::Bits;
    ///
    /// // error[E0716]: temporary value dropped while borrowed
    /// let mut base = [0b00001111, 0b11110000];
    /// let bits = Bits::from_mut(&mut base);
    ///
    /// assert_eq!(bits, Bits::new(&[0b00001111, 0b11110000]));
    /// *bits <<= 1;
    /// assert_eq!(bits, Bits::new(&[0b00011111, 0b11100000]));
    /// ```
    fn shl_assign(&mut self, shift: usize) {
        let byte_shift = shift / 8;
        let bits_shift = shift % 8;

        let end = self.byte_len() - byte_shift;
        for i in 0..end {
            let byte = self.0.get(i + byte_shift).unwrap_or(&0);
            // I use a match to avoid a panic "shift right with overflow"
            self.0[i] = match bits_shift {
                0 => *byte,
                _ => {
                    (byte << bits_shift)
                        | (self.0.get(i + byte_shift + 1).unwrap_or(&0) >> 8 - bits_shift)
                }
            };
        }
        for i in end..self.byte_len() {
            self.0[i] = 0;
        }
    }
}

impl<'s> From<&'s [u8]> for &'s Bits {
    #[inline]
    fn from(slice: &'s [u8]) -> Self {
        Bits::new(slice)
    }
}

impl<'s> From<&'s mut [u8]> for &'s mut Bits {
    #[inline]
    fn from(slice: &'s mut [u8]) -> Self {
        Bits::from_mut(slice)
    }
}

impl<'s> From<Box<[u8]>> for Box<Bits> {
    #[inline]
    fn from(value: Box<[u8]>) -> Self {
        // SAFETY: Bits is just a wrapper around [u8].
        unsafe { transmute::<Box<[u8]>, Box<Bits>>(value) }
    }
}

impl From<&Bits> for Box<Bits> {
    /// Converts a `&Bits` into a `Box<Bits>`
    ///
    /// This conversion allocates on the heap and performs a copy of the bits.
    ///
    /// # Examples
    /// ```rust
    /// use looky::bits::Bits;
    ///
    /// // create a &Bits which will be used to create a Box<Bits>
    /// let slice: &Bits = Bits::new(&[104, 101, 108, 108, 111]);
    /// let boxed_slice: Box<Bits> = Box::from(slice);
    ///
    /// println!("{boxed_slice:?}");
    /// ```
    #[inline]
    fn from(value: &Bits) -> Self {
        Bits::into_box(value)
    }
}

mod tests {
    use super::*;

    #[test]
    fn shift_by_n_16bits() {
        let bits = Bits::new(&[0b00001111, 0b11110000]);

        assert_eq!(bits << 1, Bits::new_box(&[0b00011111, 0b11100000]));
        assert_eq!(bits << 4, Bits::new_box(&[0b11111111, 0b00000000]));
        assert_eq!(bits << 7, Bits::new_box(&[0b11111000, 0b00000000]));
        assert_eq!(bits << 8, Bits::new_box(&[0b11110000, 0b00000000]));
        assert_eq!(bits << 16, Bits::new_box(&[0b00000000, 0b00000000]));
    }

    #[test]
    fn shift_assign_by_n_16bits() {
        // error[E0716]: temporary value dropped while borrowed
        let mut base = [0b00001111, 0b11110000];
        let bits = Bits::from_mut(&mut base);

        assert_eq!(bits, Bits::new(&[0b00001111, 0b11110000]));
        *bits <<= 1;
        assert_eq!(bits, Bits::new(&[0b00011111, 0b11100000]));
        *bits <<= 3;
        assert_eq!(bits, Bits::new(&[0b11111111, 0b00000000]));
        // and the rest is test with the tests of '<<' (because in internal of '<<' we use '<<=')
    }

    #[test]
    fn shift_by_n_24bits() {
        let bits = Bits::new(&[0b00001111, 0b11110000, 0b11111111]);

        assert_eq!(
            bits << 1,
            Bits::new_box(&[0b00011111, 0b11100001, 0b11111110])
        );
        assert_eq!(
            bits << 4,
            Bits::new_box(&[0b11111111, 0b00001111, 0b11110000])
        );
        assert_eq!(
            bits << 7,
            Bits::new_box(&[0b11111000, 0b01111111, 0b10000000])
        );
        assert_eq!(
            bits << 8,
            Bits::new_box(&[0b11110000, 0b11111111, 0b00000000])
        );
        assert_eq!(
            bits << 16,
            Bits::new_box(&[0b11111111, 0b00000000, 0b00000000])
        );
        assert_eq!(
            bits << 18,
            Bits::new_box(&[0b11111100, 0b00000000, 0b00000000])
        );
        assert_eq!(
            bits << 24,
            Bits::new_box(&[0b00000000, 0b00000000, 0b00000000])
        );
    }
}

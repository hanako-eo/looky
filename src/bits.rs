use core::mem::transmute;

use crate::slice::SliceIndex;

/// Bits is a array of `N*8` bits (store with an normal array, make sure it's
/// the minimum number of bytes you need)
#[derive(PartialEq, Debug)]
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
    pub fn new_box<S: AsRef<[u8]> + ?Sized>(slice: &S) -> Box<Self> {
        Self::into_box(Self::new(slice))
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
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[must_use]
    pub const fn first_bit(&self) -> Option<u8> {
        match self.0.first() {
            Some(first) => Some(*first & 0b1000000),
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
    /// This conversion allocates on the heap
    /// and performs a copy of the bits.
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

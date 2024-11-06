#[inline]
pub const fn minimal_bytes_size(bits: usize) -> usize {
    bits / 8 + (bits % 8 > 0) as usize
}

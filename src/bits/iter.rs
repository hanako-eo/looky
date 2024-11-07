use super::BitSlice;

pub struct Iter<'s> {
    pub(super) slice: &'s BitSlice,
    pub(super) index: usize,
}

impl<'s> Iterator for Iter<'s> {
    type Item = bool;

    // TODO: try to improuve it a little bit ?
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.slice.get(self.index);
        if item.is_some() {
            self.index += 1;
        }
        item
    }
}

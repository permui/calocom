pub trait ReferencePath<C> {
    fn full(&self) -> &[C];
    fn base(&self) -> &C;
    fn root(&self) -> &C;
    fn prefix(&self) -> Option<&[C]>;
    fn suffix(&self) -> Option<&[C]>;
    fn with_prefix(&self, prefix: &[C]) -> Vec<C>;
    fn with_suffix(&self, suffix: &[C]) -> Vec<C>;
}

impl<C> ReferencePath<C> for &[C]
where
    C: Clone,
{
    fn base(&self) -> &C {
        self.last().expect("reference path is empty")
    }

    fn root(&self) -> &C {
        self.first().expect("reference path is empty")
    }

    fn prefix(&self) -> Option<&[C]> {
        if !self.is_empty() {
            Some(&self[..self.len() - 1])
        } else {
            None
        }
    }

    fn suffix(&self) -> Option<&[C]> {
        if !self.is_empty() {
            Some(&self[1..])
        } else {
            None
        }
    }

    fn with_prefix(&self, prefix: &[C]) -> Vec<C> {
        let mut vec: Vec<_> = prefix.to_vec();
        vec.append(&mut self.to_vec());
        vec
    }

    fn with_suffix(&self, suffix: &[C]) -> Vec<C> {
        let mut vec = self.to_vec();
        suffix.iter().for_each(|c| vec.push(c.clone()));
        vec
    }

    fn full(&self) -> &[C] {
        self
    }
}

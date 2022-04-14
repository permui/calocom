use std::collections::HashMap;

#[derive(Debug, Default)]
pub struct UniqueName {
    history: HashMap<String, usize>,
}

impl UniqueName {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn next_name(&mut self, base: &str) -> String {
        if self.history.contains_key(base) {
            let n = self.history.get_mut(base).unwrap();
            *n += 1;
            return format!("{}.{}", base, n);
        } else {
            self.history.insert(base.to_string(), 0);
            return format!("{}.0", base);
        }
    }
}

use libc::c_char;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstCStr {
    pub data: &'static str,
}

impl ConstCStr {
    pub fn to_str(&self) -> &'static str {
        &self.data[..self.data.len() - 1]
    }

    /// Returns the wrapped string as a byte slice, **without** the NUL terminating byte.
    pub fn to_bytes(&self) -> &'static [u8] {
        self.to_str().as_bytes()
    }

    /// Returns the wrapped string as a byte slice, *with** the NUL terminating byte.
    pub fn to_bytes_with_nul(&self) -> &'static [u8] {
        self.data.as_bytes()
    }

    pub fn as_ptr(&self) -> *const c_char {
        self.data.as_bytes().as_ptr() as *const c_char
    }
}

#[macro_export]
macro_rules! const_cstr {
    ($strval:expr) => {
        $crate::aux::ConstCStr {
            data: concat!($strval, "\0"),
        }
    };
}

use libc::c_char;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstCStr {
    pub data: &'static str,
}

impl ConstCStr {
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

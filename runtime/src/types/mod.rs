use libc::c_char;
use libc::c_void;
use libc::uintptr_t;

mod enumeration;
mod tuple;
mod int;

pub use enumeration::*;
pub use tuple::*;
pub use int::*;

#[repr(u8)]
pub enum _ObjectType {
    Reserved = 0,
    Unit = 1,
    Str = 2,
    I32 = 3,
    Bool = 4,
    Tuple = 5,
    Enum = 6,
    Other = 7,
}

#[repr(C, packed(4))]
pub struct _Object {
    pub ptr: uintptr_t,
    pub tag: _ObjectType,
    pub reserved1: u8,
    pub reserved2: u16,
}

#[repr(C, packed)]
pub struct _String {
    pub header: _Object,
    pub len: u32,
    pub data: [c_char; 0],
}

#[repr(C, packed)]
pub struct _Int32 {
    pub header: _Object,
    pub data: i32,
}

#[repr(C, packed)]
pub struct _Tuple {
    pub header: _Object,
    pub data: [*mut c_void; 0],
}

#[repr(C, packed)]
pub struct _Unit {
    pub header: _Object,
}

#[repr(C, packed)]
pub struct _Enum {
    pub header: _Object,
    pub discriminant: u32,
    pub variant: *mut c_void,
}

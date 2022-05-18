use libc::c_char;
use libc::c_void;
use libc::uintptr_t;

mod enumeration;
mod int;
mod tuple;

pub use enumeration::*;
pub use int::*;
pub use tuple::*;

#[repr(u8)]
pub enum _ObjectType {
    Reserved = 0,
    Unit = 1,
    Str = 2,
    Bool = 3,
    Int32 = 4,
    Float64 = 5,
    Tuple = 6,
    Enum = 7,
    Other = 8,
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

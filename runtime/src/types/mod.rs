use libc::c_char;
use libc::c_void;
use libc::uintptr_t;

mod array;
mod boolean;
mod closure;
mod enumeration;
mod float;
mod int;
mod string;
mod tuple;
mod conversion;
mod comparison;

pub use array::*;
pub use boolean::*;
pub use closure::*;
pub use enumeration::*;
pub use float::*;
pub use int::*;
pub use string::*;
pub use tuple::*;
pub use conversion::*;
pub use comparison::*;

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
    Closure = 8,
    Array = 9,
    Other = 10,
}

#[repr(C, packed(4))]
pub struct _Object {
    pub ptr: uintptr_t,
    pub tag: _ObjectType,
    pub reserved1: u8,
    pub reserved2: u16,
}

#[repr(C)]
pub struct _String {
    pub header: _Object,
    pub len: u32,
    pub data: [c_char; 0],
}

#[repr(C)]
pub struct _Int32 {
    pub header: _Object,
    pub data: i32,
}

#[repr(C)]
pub struct _Float64 {
    pub header: _Object,
    pub data: f64,
}

#[repr(C)]
pub struct _Tuple {
    pub header: _Object,
    pub length: u32,
    pub data: [*mut _Object; 0],
}

#[repr(C)]
pub struct _Unit {
    pub header: _Object,
}

#[repr(C)]
pub struct _Enum {
    pub header: _Object,
    pub discriminant: u32,
    pub variant: *mut c_void,
}

#[repr(C)]
pub struct _Closure {
    pub header: _Object,
    pub env_len: u32,
    pub env: *mut [*mut _Object; 0],
    pub fn_ptr: [*mut c_void; 0],
}

#[repr(C)]
pub struct _Array {
    pub header: _Object,
    pub length: u32,
    pub data: *mut [*mut _Object; 0],
    pub capacity: u32,
}

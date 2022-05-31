use super::_Closure;
use super::_Object;
use super::_ObjectType;
use crate::alloc::alloc;
use crate::panic::panic;

use libc::c_void;
use libc::memcpy;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_create_closure"]
pub unsafe extern "C" fn create_closure(
    captured: *mut [*mut _Object; 0],
    length: u32,
) -> *mut _Closure {
    let mem = alloc(::core::mem::size_of::<_Closure>() + ::core::mem::size_of::<*mut c_void>())
        as *mut _Closure;
    let env_size = length as usize * ::core::mem::size_of::<*mut _Object>();
    let env = alloc(env_size) as *mut [*mut _Object; 0];

    (*mem).header.tag = _ObjectType::Closure;
    (*mem).env_len = length as u32;
    (*mem).env = env;

    // copy the environment
    memcpy(env as *mut c_void, captured as *mut c_void, env_size);
    mem
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_extract_closure_capture"]
pub unsafe extern "C" fn extract_closure_capture(
    closure: *mut _Closure,
    index: i32,
) -> *mut _Object {
    if index < 0 || index as u32 > (*closure).env_len {
        panic(const_cstr!("try to extract a nonexistent closure capture").as_ptr());
    }
    ((*closure).env as *mut *mut _Object)
        .add(index as usize)
        .read()
}

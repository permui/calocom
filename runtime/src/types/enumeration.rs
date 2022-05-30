use super::_Enum;
use super::_Object;
use super::_ObjectType;
use super::_Tuple;
use super::tuple::extract_tuple_field;
use crate::alloc::alloc;
use crate::panic::panic;

use libc::c_void;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_enum"]
pub extern "C" fn alloc_enum() -> *mut _Enum {
    let mem = alloc(::core::mem::size_of::<_Enum>()) as *mut _Enum;
    unsafe {
        (*mem).header.tag = _ObjectType::Enum;
    }
    mem
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_enum_tag"]
pub unsafe extern "C" fn extract_enum_tag(e: *const _Enum) -> i32 {
    (*e).discriminant as i32
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_enum_field"]
pub unsafe extern "C" fn extract_enum_field(
    e: *mut _Enum,
    ctor_index: i32,
    field_index: i32,
) -> *mut _Object {
    if (*e).discriminant != ctor_index as u32 {
        panic(const_cstr!("the target enum doesn't carry the expected variant").as_ptr());
    }
    let variant = (*e).variant as *mut _Tuple;
    extract_tuple_field(variant, field_index)
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_construct_enum"]
pub extern "C" fn construct_enum(tag: i32, obj: *mut _Object) -> *mut _Enum {
    let mem = alloc_enum();
    unsafe {
        (*mem).discriminant = tag as u32;
        (*mem).variant = obj as *mut c_void;
    }
    mem
}

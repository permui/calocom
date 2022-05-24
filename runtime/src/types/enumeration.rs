use super::_Enum;
use super::_Object;
use super::_Tuple;
use super::tuple::extract_tuple_field;
use crate::alloc::alloc_enum;
use crate::panic::panic;
use libc::c_void;

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
        let fmt = const_cstr!("the target enum doesn't carry the expected variant");
        panic(fmt.as_ptr());
    }
    let variant = (*e).variant as *mut _Tuple;
    extract_tuple_field(variant, field_index)
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_construct_enum"]
pub extern "C" fn construct(tag: i32, obj: *mut _Object) -> *mut _Enum {
    let mem = alloc_enum();
    unsafe {
        (*mem).discriminant = tag as u32;
        (*mem).variant = obj as *mut c_void;
    }
    mem
}

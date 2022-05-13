use super::_Object;
use super::_Tuple;

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_tuple_field"]
pub unsafe extern "C" fn extract_tuple_field(e: *mut _Tuple, field_index: i32) -> *mut _Object {
    (*e).data[field_index as usize] as *mut _Object
}

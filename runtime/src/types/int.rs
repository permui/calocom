use super::_Int32;

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_i32"]
pub unsafe extern "C" fn extract_i32(obj: *mut _Int32, _dummy: i32) -> i32 {
    (*obj).data
}

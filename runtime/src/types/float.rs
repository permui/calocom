use super::_Float64;

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_f64"]
pub unsafe extern "C" fn extract_f64(obj: *mut _Float64, _dummy: i32) -> f64 {
    (*obj).data
}

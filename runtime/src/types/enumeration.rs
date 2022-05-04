use crate::types::_Enum;

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_enum_tag"]
pub unsafe extern "C" fn extract_enum_tag(e: *const _Enum) -> i32 {
    (*e).discriminator as i32
}

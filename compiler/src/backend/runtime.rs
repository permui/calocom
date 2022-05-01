use inkwell::module::{Module, Linkage};
use inkwell::values::FunctionValue;
use paste::paste;

use super::memory::MemoryLayoutContext;

macro_rules! runtime_function {
    ($fn_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf>; }
    };
}

macro_rules! runtime_function_name_string {
    ($fn_name:ident) => {
        concat!("__calocom_runtime_", stringify!($fn_name))
    };
}

macro_rules! runtime_function_impl_for_llvm_module {
    ($fn_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf> {
            self.get_function(runtime_function_name_string!($fn_name)).expect("runtime function not found")
        } }
    };
}

trait CoreLibrary<'ctx> {
    runtime_function!(alloc, 'ctx);
    runtime_function!(alloc_object, 'ctx);
    runtime_function!(alloc_unit, 'ctx);
    runtime_function!(alloc_string, 'ctx);
    runtime_function!(alloc_string_literal, 'ctx);
    runtime_function!(print_object, 'ctx);
    fn initialize_runtime_function(
        &self,
        module: &'ctx Module<'ctx>,
        ctx: &'ctx MemoryLayoutContext,
    );
}

impl<'ctx> CoreLibrary<'ctx> for Module<'ctx> {
    runtime_function_impl_for_llvm_module!(alloc, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_object, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_unit, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_string, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_string_literal, 'ctx);
    runtime_function_impl_for_llvm_module!(print_object, 'ctx);
    fn initialize_runtime_function(
        &self,
        module: &'ctx Module<'ctx>,
        ctx: &'ctx MemoryLayoutContext,
    ) {
    }
}

use std::path::Path;

use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::{Linkage, Module};
use inkwell::types::StructType;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;
use paste::paste;

use crate::midend::type_context::{PrimitiveType, SingletonType};

macro_rules! runtime_function {
    ($fn_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf>; }
    };
}

macro_rules! runtime_type {
    ($ty_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_type_ $ty_name>] (&self) -> StructType<$lf>; }
    };
}

macro_rules! runtime_type_name_string {
    ($type_name:ident) => {
        concat!("core::", stringify!($type_name))
    };
}

macro_rules! runtime_function_name_string {
    ($fn_name:ident) => {
        concat!("__calocom_runtime_", stringify!($fn_name))
    };
}

macro_rules! runtime_function_getter {
    ($fn_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf> {
            self.get_function(runtime_function_name_string!($fn_name)).expect("runtime function not found")
        } }
    };
}

macro_rules! runtime_type_getter {
    ($ty_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_type_ $ty_name>] (&self) -> StructType<$lf> {
            self.get_struct_type(runtime_type_name_string!($ty_name)).expect("runtime type not found")
        } }
    };
}

pub trait CoreLibrary<'ctx> {
    runtime_function!(panic, 'ctx);
    runtime_function!(alloc, 'ctx);
    runtime_function!(alloc_object, 'ctx);
    runtime_function!(alloc_unit, 'ctx);
    runtime_function!(alloc_string, 'ctx);
    runtime_function!(alloc_string_literal, 'ctx);
    runtime_function!(print_object, 'ctx);
    runtime_type!(_Object, 'ctx);
    runtime_type!(_Unit, 'ctx);
    runtime_type!(_Tuple, 'ctx);
    runtime_type!(_Int32, 'ctx);
    runtime_type!(_String, 'ctx);
    fn get_calocom_type(&self, ty: PrimitiveType) -> BasicTypeEnum<'ctx>;
    fn link_calocom_runtime_module(&mut self, path: &Path);
}

impl<'ctx> CoreLibrary<'ctx> for Module<'ctx> {
    runtime_function_getter!(panic, 'ctx);
    runtime_function_getter!(alloc, 'ctx);
    runtime_function_getter!(alloc_object, 'ctx);
    runtime_function_getter!(alloc_unit, 'ctx);
    runtime_function_getter!(alloc_string, 'ctx);
    runtime_function_getter!(alloc_string_literal, 'ctx);
    runtime_function_getter!(print_object, 'ctx);

    runtime_type_getter!(_Object, 'ctx);
    runtime_type_getter!(_Unit, 'ctx);
    runtime_type_getter!(_Tuple, 'ctx);
    runtime_type_getter!(_Int32, 'ctx);
    runtime_type_getter!(_String, 'ctx);

    fn get_calocom_type(&self, ty: PrimitiveType) -> BasicTypeEnum<'ctx> {
        let context = unsafe { &*(&*self.get_context() as *const Context) };
        match ty {
            PrimitiveType::Object => self.get_runtime_type__Object().into(),
            PrimitiveType::Str => self.get_runtime_type__String().into(),
            PrimitiveType::Bool => self.get_runtime_type__Int32().into(),
            PrimitiveType::Int32 => self.get_runtime_type__Int32().into(),
            PrimitiveType::Unit => self.get_runtime_type__Unit().into(),
            PrimitiveType::CInt32 => context.i32_type().into(),
        }
    }

    fn link_calocom_runtime_module(&mut self, path: &Path) {
        let memory_buffer =
            MemoryBuffer::create_from_file(&path).expect("read runtime file failed");
        let context = unsafe { &*(&*self.get_context() as *const Context) };
        let runtime_module = context
            .create_module_from_ir(memory_buffer)
            .expect("unable to make runtime module");
        self.link_in_module(runtime_module)
            .expect("unable to link runtime module");
    }
}

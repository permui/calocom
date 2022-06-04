use std::path::Path;

use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::types::BasicTypeEnum;
use inkwell::types::StructType;
use inkwell::values::FunctionValue;
use paste::paste;

use crate::backend::name_mangling::Mangling;
use crate::common::name_context::NameContext;
use crate::common::type_context::CallKind;
use crate::common::type_context::Primitive;
use crate::common::type_context::TypeContext;
use crate::common::type_context::TypeRef;

macro_rules! runtime_function {
    ($fn_name:ident, $lf: lifetime) => {
        paste! {
            #[allow(non_snake_case)]
            fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf>;
        }
    };
}

macro_rules! runtime_type {
    ($ty_name:ident, $lf: lifetime) => {
        paste! {
            #[allow(non_snake_case)]
            fn [<get_runtime_type_ $ty_name>] (&self) -> StructType<$lf>;
        }
    };
}

macro_rules! runtime_type_name_string {
    ($type_name:ident) => {
        concat!("types::", stringify!($type_name))
    };
}

macro_rules! runtime_function_name_string {
    ($fn_name:ident) => {
        concat!("__calocom_runtime_", stringify!($fn_name))
    };
}

macro_rules! runtime_function_getter {
    ($fn_name:ident, $lf: lifetime) => {
        paste! {
            #[allow(non_snake_case)]
            fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf> {
                self.get_function(runtime_function_name_string!($fn_name)).expect("runtime function not found")
            }
        }
    };
}

macro_rules! runtime_type_getter {
    ($ty_name:ident, $lf: lifetime) => {
        paste! {
            #[allow(non_snake_case)]
            fn [<get_runtime_type_ $ty_name>] (&self) -> StructType<$lf> {
                self.get_struct_type(runtime_type_name_string!($ty_name)).expect("runtime type not found")
            }
        }
    };
}

macro_rules! declare_library_function {
    ($name_ctx: expr, $ty_ctx: expr; $($fn_name: ident).+ : || => $ret_type: ident) => {
        $name_ctx
            .insert_fully_qualified_symbol(
                [$(stringify!($fn_name)),+].map(|s| s.to_string()).to_vec(),
                $ty_ctx.callable_type(CallKind::Function, $ret_type, [].to_vec(), false),
            )
            .and_then(|_| -> Option<()> { unreachable!() });
    };
    ($name_ctx: expr, $ty_ctx: expr; $($fn_name: ident).+ : | $($param_type: ident),* | => $ret_type: ident) => {
        $name_ctx
            .insert_fully_qualified_symbol(
                [$(stringify!($fn_name)),+].map(|s| s.to_string()).to_vec(),
                $ty_ctx.callable_type(CallKind::Function, $ret_type, [$($param_type),*].to_vec(), false),
            )
            .and_then(|_| -> Option<()> { unreachable!() });
    };
}

macro_rules! insert_library_function {
    ($name_ctx: expr, $ty_ctx: expr, $module: expr; $($fn_name: ident).+ : || => $ret_type: ident) => {
        let path = [$(stringify!($fn_name)),+].map(|s| s.to_string()).to_vec();
        let path_ref = &path.as_slice();
        let decorated_name = $ty_ctx.get_mangled_polymorphic_function_name(path_ref, $ret_type, &[]);
        let function = $module
            .get_function(decorated_name.as_str())
            .unwrap_or_else(|| {
                panic!(
                    "function {}: {:?} doesn't exist",
                    path.join("."),
                    decorated_name.as_str()
                )
            });

        $name_ctx
            .insert_fully_qualified_symbol(path, function)
            .and_then(|_| -> Option<()> { unreachable!() });
    };
    ($name_ctx: expr, $ty_ctx: expr, $module: expr; $($fn_name: ident).+ : | $($param_type: ident),* | => $ret_type: ident) => {
        let path = [$(stringify!($fn_name)),+].map(|s| s.to_string()).to_vec();
        let path_ref = &path.as_slice();
        let decorated_name = $ty_ctx.get_mangled_polymorphic_function_name(path_ref, $ret_type, [$($param_type),*].to_vec().as_slice());
        let function = $module
            .get_function(decorated_name.as_str())
            .unwrap_or_else(|| {
                panic!(
                    "function {}: {:?} doesn't exist",
                    path.join("."),
                    decorated_name.as_str()
                )
            });

        $name_ctx
            .insert_fully_qualified_symbol(path, function)
            .and_then(|_| -> Option<()> { unreachable!() });
    };
}

#[derive(PartialEq, Eq)]
pub enum RuntimeType {
    Object,
    Str,
    Bool,
    Int32,
    Unit,
    Float64,
    CInt32,
    Array,
    Closure,
    Enum,
    Tuple,
}

impl From<Primitive> for RuntimeType {
    fn from(prim: Primitive) -> Self {
        match prim {
            Primitive::Object => Self::Object,
            Primitive::Unit => Self::Unit,
            Primitive::Str => Self::Str,
            Primitive::Bool => Self::Bool,
            Primitive::Int32 => Self::Int32,
            Primitive::Float64 => Self::Float64,
            Primitive::CInt32 => Self::CInt32,
        }
    }
}

pub trait CoreLibrary<'ctx> {
    runtime_function!(panic, 'ctx);
    runtime_function!(entry_panic_block, 'ctx);

    runtime_function!(print_object, 'ctx);

    runtime_function!(alloc, 'ctx);
    runtime_function!(alloc_object, 'ctx);
    runtime_function!(alloc_unit, 'ctx);

    runtime_function!(alloc_string, 'ctx);
    runtime_function!(alloc_string_literal, 'ctx);
    runtime_function!(extract_cstr, 'ctx);
    runtime_function!(get_string_length, 'ctx);
    runtime_function!(append_buffer_to_string, 'ctx);

    runtime_function!(alloc_i32, 'ctx);
    runtime_function!(alloc_i32_literal, 'ctx);
    runtime_function!(extract_i32, 'ctx);
    runtime_function!(increase_i32, 'ctx);

    runtime_function!(alloc_bool, 'ctx);
    runtime_function!(alloc_bool_literal, 'ctx);
    runtime_function!(extract_bool, 'ctx);

    runtime_function!(alloc_f64, 'ctx);
    runtime_function!(alloc_f64_literal, 'ctx);
    runtime_function!(extract_f64, 'ctx);
    runtime_function!(increase_f64, 'ctx);

    runtime_function!(alloc_tuple, 'ctx);
    runtime_function!(get_tuple_length, 'ctx);
    runtime_function!(extract_tuple_field, 'ctx);
    runtime_function!(construct_tuple_1, 'ctx);
    runtime_function!(construct_tuple_2, 'ctx);
    runtime_function!(construct_tuple_3, 'ctx);
    runtime_function!(construct_tuple_4, 'ctx);
    runtime_function!(construct_tuple_5, 'ctx);
    runtime_function!(construct_tuple_6, 'ctx);
    runtime_function!(construct_tuple_7, 'ctx);
    runtime_function!(construct_tuple_8, 'ctx);

    runtime_function!(alloc_enum, 'ctx);
    runtime_function!(extract_enum_field, 'ctx);
    runtime_function!(extract_enum_tag, 'ctx);
    runtime_function!(construct_enum, 'ctx);

    runtime_function!(allow_array, 'ctx);
    runtime_function!(array_index, 'ctx);
    runtime_function!(get_array_length, 'ctx);

    runtime_function!(create_closure, 'ctx);
    runtime_function!(extract_closure_capture, 'ctx);
    runtime_function!(i32_to_f64, 'ctx);
    runtime_function!(f64_to_i32, 'ctx);

    runtime_function!(compare_string, 'ctx);
    runtime_function!(compare_string_with_cstr, 'ctx);

    runtime_type!(_Object, 'ctx);
    runtime_type!(_Unit, 'ctx);
    runtime_type!(_Tuple, 'ctx);
    runtime_type!(_Int32, 'ctx);
    runtime_type!(_Float64, 'ctx);
    runtime_type!(_String, 'ctx);
    runtime_type!(_Enum, 'ctx);
    runtime_type!(_Array, 'ctx);
    runtime_type!(_Closure, 'ctx);

    fn get_calocom_type(&self, ty: RuntimeType) -> BasicTypeEnum<'ctx>;
    fn link_calocom_runtime_module(&self, path: &Path);
}

impl<'ctx> CoreLibrary<'ctx> for Module<'ctx> {
    runtime_function_getter!(panic, 'ctx);
    runtime_function_getter!(entry_panic_block, 'ctx);

    runtime_function_getter!(print_object, 'ctx);

    runtime_function_getter!(alloc, 'ctx);
    runtime_function_getter!(alloc_object, 'ctx);
    runtime_function_getter!(alloc_unit, 'ctx);

    runtime_function_getter!(alloc_string, 'ctx);
    runtime_function_getter!(alloc_string_literal, 'ctx);
    runtime_function_getter!(extract_cstr, 'ctx);
    runtime_function_getter!(get_string_length, 'ctx);
    runtime_function_getter!(append_buffer_to_string, 'ctx);

    runtime_function_getter!(alloc_i32, 'ctx);
    runtime_function_getter!(alloc_i32_literal, 'ctx);
    runtime_function_getter!(extract_i32, 'ctx);
    runtime_function_getter!(increase_i32, 'ctx);

    runtime_function_getter!(alloc_bool, 'ctx);
    runtime_function_getter!(alloc_bool_literal, 'ctx);
    runtime_function_getter!(extract_bool, 'ctx);

    runtime_function_getter!(alloc_f64, 'ctx);
    runtime_function_getter!(alloc_f64_literal, 'ctx);
    runtime_function_getter!(extract_f64, 'ctx);
    runtime_function_getter!(increase_f64, 'ctx);

    runtime_function_getter!(alloc_tuple, 'ctx);
    runtime_function_getter!(get_tuple_length, 'ctx);
    runtime_function_getter!(extract_tuple_field, 'ctx);
    runtime_function_getter!(construct_tuple_1, 'ctx);
    runtime_function_getter!(construct_tuple_2, 'ctx);
    runtime_function_getter!(construct_tuple_3, 'ctx);
    runtime_function_getter!(construct_tuple_4, 'ctx);
    runtime_function_getter!(construct_tuple_5, 'ctx);
    runtime_function_getter!(construct_tuple_6, 'ctx);
    runtime_function_getter!(construct_tuple_7, 'ctx);
    runtime_function_getter!(construct_tuple_8, 'ctx);

    runtime_function_getter!(alloc_enum, 'ctx);
    runtime_function_getter!(extract_enum_field, 'ctx);
    runtime_function_getter!(extract_enum_tag, 'ctx);
    runtime_function_getter!(construct_enum, 'ctx);

    runtime_function_getter!(allow_array, 'ctx);
    runtime_function_getter!(array_index, 'ctx);
    runtime_function_getter!(get_array_length, 'ctx);

    runtime_function_getter!(create_closure, 'ctx);
    runtime_function_getter!(extract_closure_capture, 'ctx);

    runtime_function_getter!(i32_to_f64, 'ctx);
    runtime_function_getter!(f64_to_i32, 'ctx);

    runtime_function_getter!(compare_string, 'ctx);
    runtime_function_getter!(compare_string_with_cstr, 'ctx);

    runtime_type_getter!(_Object, 'ctx);
    runtime_type_getter!(_Unit, 'ctx);
    runtime_type_getter!(_Tuple, 'ctx);
    runtime_type_getter!(_Int32, 'ctx);
    runtime_type_getter!(_Float64, 'ctx);
    runtime_type_getter!(_String, 'ctx);
    runtime_type_getter!(_Enum, 'ctx);
    runtime_type_getter!(_Array, 'ctx);
    runtime_type_getter!(_Closure, 'ctx);

    fn get_calocom_type(&self, ty: RuntimeType) -> BasicTypeEnum<'ctx> {
        let context = unsafe { &*(&*self.get_context() as *const Context) };
        match ty {
            RuntimeType::Object => self.get_runtime_type__Object().into(),
            RuntimeType::Str => self.get_runtime_type__String().into(),
            RuntimeType::Bool => self.get_runtime_type__Int32().into(),
            RuntimeType::Int32 => self.get_runtime_type__Int32().into(),
            RuntimeType::Unit => self.get_runtime_type__Unit().into(),
            RuntimeType::Float64 => self.get_runtime_type__Float64().into(),
            RuntimeType::CInt32 => context.i32_type().into(),
            RuntimeType::Array => self.get_runtime_type__Array().into(),
            RuntimeType::Closure => self.get_runtime_type__Closure().into(),
            RuntimeType::Enum => self.get_runtime_type__Enum().into(),
            RuntimeType::Tuple => self.get_runtime_type__Tuple().into(),
        }
    }

    fn link_calocom_runtime_module(&self, path: &Path) {
        let memory_buffer = MemoryBuffer::create_from_file(path).expect("read runtime file failed");
        let context = unsafe { &*(&*self.get_context() as *const Context) };
        let runtime_module = context
            .create_module_from_ir(memory_buffer)
            .expect("unable to make runtime module");
        self.link_in_module(runtime_module)
            .expect("unable to link runtime module");
    }
}

pub fn create_library_function_signature(
    name_ctx: &mut NameContext<TypeRef>,
    type_ctx: &mut TypeContext,
) {
    let unit = type_ctx.primitive_type(Primitive::Unit);
    let object = type_ctx.primitive_type(Primitive::Object);
    let string = type_ctx.primitive_type(Primitive::Str);
    let t_i32 = type_ctx.primitive_type(Primitive::Int32);
    let t_f64 = type_ctx.primitive_type(Primitive::Float64);
    let arr_of_str = type_ctx.array_type(string);
    let arr_of_obj = type_ctx.array_type(object);

    declare_library_function!(name_ctx, type_ctx; std.io.print: |object| => unit);
    declare_library_function!(name_ctx, type_ctx; std.io.println: |object| => unit);
    declare_library_function!(name_ctx, type_ctx; std.io.print_i32_with_align: |t_i32, string, t_i32| => unit);
    declare_library_function!(name_ctx, type_ctx; std.io.readln: || => string);
    declare_library_function!(name_ctx, type_ctx; std.io.read_f64: || => t_f64);
    declare_library_function!(name_ctx, type_ctx; std.io.read_i32: || => t_i32);
    declare_library_function!(name_ctx, type_ctx; std.string.split: |string, string| => arr_of_str);
    declare_library_function!(name_ctx, type_ctx; std.array.new: |t_i32, object| => arr_of_obj);
    declare_library_function!(name_ctx, type_ctx; std.array.len: |object| => t_i32);
}

pub fn insert_library_function<'ctx>(
    name_ctx: &mut NameContext<FunctionValue<'ctx>>,
    type_ctx: &mut TypeContext,
    module: &Module<'ctx>,
) {
    let unit = type_ctx.primitive_type(Primitive::Unit);
    let object = type_ctx.primitive_type(Primitive::Object);
    let string = type_ctx.primitive_type(Primitive::Str);
    let t_i32 = type_ctx.primitive_type(Primitive::Int32);
    let t_f64 = type_ctx.primitive_type(Primitive::Float64);
    let arr_of_str = type_ctx.array_type(string);
    let arr_of_obj = type_ctx.array_type(object);

    insert_library_function!(name_ctx, type_ctx, module; std.io.print: |object| => unit);
    insert_library_function!(name_ctx, type_ctx, module; std.io.println: |object| => unit);
    insert_library_function!(name_ctx, type_ctx, module; std.io.print_i32_with_align: |t_i32, string, t_i32| => unit);
    insert_library_function!(name_ctx, type_ctx, module; std.io.readln: || => string);
    insert_library_function!(name_ctx, type_ctx, module; std.io.read_f64: || => t_f64);
    insert_library_function!(name_ctx, type_ctx, module; std.io.read_i32: || => t_i32);
    insert_library_function!(name_ctx, type_ctx, module; std.string.split: |string, string| => arr_of_str);
    insert_library_function!(name_ctx, type_ctx, module; std.array.new: |t_i32, object| => arr_of_obj);
    insert_library_function!(name_ctx, type_ctx, module; std.array.len: |object| => t_i32);
}

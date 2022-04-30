use std::collections::HashMap;
use std::fmt::format;
use std::hash::Hash;
use std::pin::Pin;
use std::rc::Rc;

use crate::midend::*;

use inkwell::builder::{self, Builder};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicTypeEnum, PointerType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::AddressSpace;
use paste::paste;

macro_rules! runtime_function {
    ($fn_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf>; }
    };
}

macro_rules! runtime_function_impl_for_llvm_module {
    ($fn_name:ident, $lf: lifetime) => {
        paste! { fn [<get_runtime_function_ $fn_name>] (&self) -> FunctionValue<$lf> {
            self.get_function(concat!("__calocom_runtime_", stringify!($fn_name))).expect("runtime function not found")
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
}

impl<'ctx> CoreLibrary<'ctx> for Module<'ctx> {
    runtime_function_impl_for_llvm_module!(alloc, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_object, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_unit, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_string, 'ctx);
    runtime_function_impl_for_llvm_module!(alloc_string_literal, 'ctx);
    runtime_function_impl_for_llvm_module!(print_object, 'ctx);
}

fn get_ptr_type_of_basic_type_enum(typ: BasicTypeEnum<'_>) -> PointerType<'_> {
    let g = AddressSpace::Generic;
    match typ {
        BasicTypeEnum::ArrayType(x) => x.ptr_type(g),
        BasicTypeEnum::FloatType(x) => x.ptr_type(g),
        BasicTypeEnum::IntType(x) => x.ptr_type(g),
        BasicTypeEnum::PointerType(x) => x.ptr_type(g),
        BasicTypeEnum::StructType(x) => x.ptr_type(g),
        BasicTypeEnum::VectorType(x) => x.ptr_type(g),
    }
}

trait MemoryType<'ctx> {
    fn get_type(&self) -> BasicTypeEnum<'ctx>;
    fn get_common_type(&self) -> BasicTypeEnum<'ctx> {
        self.get_type()
    }
    fn get_boxed_type(&self) -> PointerType<'ctx> {
        get_ptr_type_of_basic_type_enum(self.get_type())
    }
    fn get_boxed_common_type(&self) -> PointerType<'ctx> {
        get_ptr_type_of_basic_type_enum(self.get_common_type())
    }
}

trait BoxedValue<'ctx> {
    fn unbox(self, builder: &'ctx Builder) -> BasicValueEnum<'ctx>;
}

trait MemoryValue<'ctx> {
    fn get_value(&self, builder: &'ctx Builder) -> BasicValueEnum<'ctx> {
        self.get_boxed_value(builder).unbox(builder)
    }

    fn get_boxed_value(&self, builder: &'ctx Builder) -> PointerValue<'ctx> {
        let ptr = self.get_stack_slot(builder);
        builder.build_load(ptr, "").into_pointer_value()
    }

    fn get_tag_value(&self, builder: &'ctx Builder) -> IntValue<'ctx>;
    fn get_reserved1_value(&self, builder: &'ctx Builder) -> IntValue<'ctx>;
    fn get_reserved2_value(&self, builder: &'ctx Builder) -> IntValue<'ctx>;
    fn get_stack_slot(&self, builder: &'ctx Builder) -> PointerValue<'ctx>;
    fn allocate_stack_slot(&mut self, builder: &'ctx Builder);
}

trait Initializable<'ctx> {
    fn initialize(&mut self, module: &'ctx Module, builder: &'ctx Builder);
}

trait LiteralConstructible<'ctx> {
    fn create_literal<T>(&self, builder: &'ctx Builder, data: T);
}

impl<'ctx> BoxedValue<'ctx> for PointerValue<'ctx> {
    fn unbox(self, builder: &'ctx Builder) -> BasicValueEnum<'ctx> {
        builder.build_load(self, "")
    }
}

enum MemoryLayout<'ctx> {
    Object(ObjectLayout<'ctx>),
    Enum(EnumLayout<'ctx>),
    Tuple(TupleLayout<'ctx>),
}

struct ObjectLayout<'ctx> {
    context: &'ctx Context,
    stack_slot: Option<PointerValue<'ctx>>,
}

impl<'ctx> MemoryType<'ctx> for ObjectLayout<'ctx> {
    fn get_type(&self) -> BasicTypeEnum<'ctx> {
        let i64_t = self.context.i64_type();
        let i8_t = self.context.i8_type();
        let i16_t = self.context.i16_type();
        let typ = self.context.struct_type(
            &[i64_t.into(), i8_t.into(), i8_t.into(), i16_t.into()],
            true,
        );
        typ.into()
    }
}

impl<'ctx> MemoryValue<'ctx> for ObjectLayout<'ctx> {
    fn get_tag_value(&self, builder: &'ctx Builder) -> IntValue<'ctx> {
        let boxed = self.get_boxed_value(builder);
        let tag_ptr;
        unsafe {
            // [ptr, tag, reserved1, reserved2]
            tag_ptr = builder.build_in_bounds_gep(
                boxed,
                &[
                    self.context.i64_type().const_int(0, false),
                    self.context.i32_type().const_int(1, false),
                ],
                "",
            );
        }
        builder.build_load(tag_ptr, "").into_int_value()
    }

    fn get_reserved1_value(&self, builder: &'ctx Builder) -> IntValue<'ctx> {
        let boxed = self.get_boxed_value(builder);
        let res1;
        unsafe {
            // [ptr, tag, reserved1, reserved2]
            res1 = builder.build_in_bounds_gep(
                boxed,
                &[
                    self.context.i64_type().const_int(0, false),
                    self.context.i32_type().const_int(2, false),
                ],
                "",
            );
        }
        builder.build_load(res1, "").into_int_value()
    }

    fn get_reserved2_value(&self, builder: &'ctx Builder) -> IntValue<'ctx> {
        let boxed = self.get_boxed_value(builder);
        let res2;
        unsafe {
            // [ptr, tag, reserved1, reserved2]
            res2 = builder.build_in_bounds_gep(
                boxed,
                &[
                    self.context.i64_type().const_int(0, false),
                    self.context.i32_type().const_int(3, false),
                ],
                "",
            );
        }
        builder.build_load(res2, "").into_int_value()
    }

    fn get_stack_slot(&self, builder: &'ctx Builder) -> PointerValue<'ctx> {
        let mut ptr = self.stack_slot.expect("stack slot need to be allocated");
        if ptr.get_type() != self.get_boxed_type().ptr_type(AddressSpace::Generic) {
            ptr = builder
                .build_bitcast(
                    ptr,
                    self.get_boxed_type().ptr_type(AddressSpace::Generic),
                    "",
                )
                .into_pointer_value();
        }
        ptr
    }

    fn allocate_stack_slot(&mut self, builder: &'ctx Builder) {
        if self.stack_slot.is_some() {
            panic!("stack slot has been allocated")
        }
        self.stack_slot = Some(builder.build_alloca(self.get_boxed_type(), ""))
    }
}

impl<'ctx> Initializable<'ctx> for ObjectLayout<'ctx> {
    fn initialize(&mut self, module: &'ctx Module, builder: &'ctx Builder) {
        let ret = builder
            .build_call(module.get_runtime_function_alloc_object(), &[], "")
            .try_as_basic_value()
            .left()
            .expect("runtime function has wrong return type");
        let slot = self.get_stack_slot(builder);
        builder.build_store(slot, ret);
    }
}

struct TupleLayout<'ctx> {
    base: ObjectLayout<'ctx>,
    fields: Vec<&'ctx dyn MemoryType<'ctx>>,
}

impl<'ctx> MemoryType<'ctx> for TupleLayout<'ctx> {
    fn get_common_type(&self) -> BasicTypeEnum<'ctx> {
        let header_typ = self.base.get_type();
        let i8_0_t = self
            .base
            .context
            .i8_type()
            .ptr_type(AddressSpace::Generic)
            .array_type(0);
        let typ = self
            .base
            .context
            .struct_type(&[header_typ, i8_0_t.into()], true)
            .into();
        typ
    }

    fn get_type(&self) -> BasicTypeEnum<'ctx> {
        let header_typ = self.base.get_type();
        let mut tuple_typ: Vec<BasicTypeEnum> = vec![header_typ];
        let mut field_typ = self
            .fields
            .iter()
            .map(|ty| ty.get_boxed_type().into())
            .collect::<Vec<BasicTypeEnum>>();
        tuple_typ.append(&mut field_typ);
        let typ = self.base.context.struct_type(&tuple_typ[..], true).into();
        typ
    }
}

impl<'ctx> MemoryValue<'ctx> for TupleLayout<'ctx> {
    fn get_tag_value(&self, builder: &'ctx Builder) -> IntValue<'ctx> {
        self.base.get_tag_value(builder)
    }

    fn get_reserved1_value(&self, builder: &'ctx Builder) -> IntValue<'ctx> {
        self.base.get_reserved1_value(builder)
    }

    fn get_reserved2_value(&self, builder: &'ctx Builder) -> IntValue<'ctx> {
        self.base.get_reserved2_value(builder)
    }

    fn get_stack_slot(&self, _builder: &'ctx Builder) -> PointerValue<'ctx> {
        self.base
            .stack_slot
            .expect("stack slot need to be allocated")
    }

    fn allocate_stack_slot(&mut self, builder: &'ctx Builder) {
        if self.base.stack_slot.is_some() {
            panic!("stack slot has been allocated")
        }
        self.base.stack_slot = Some(builder.build_alloca(self.get_boxed_type(), ""))
    }
}

impl<'ctx> TupleLayout<'ctx> {
    fn get_nth_field_type(&self, n: usize) -> BasicTypeEnum<'ctx> {
        self.fields[n].get_type()
    }

    fn get_nth_filed_boxed_type(&self, n: usize) -> BasicTypeEnum<'ctx> {
        self.fields[n].get_boxed_type().into()
    }

    fn get_nth_field_value(&self, n: usize, builder: &'ctx Builder) -> BasicValueEnum<'ctx> {
        self.get_nth_filed_boxed_value(n, builder).unbox(builder)
    }

    fn get_nth_filed_boxed_value(&self, n: usize, builder: &'ctx Builder) -> PointerValue<'ctx> {
        let boxed = self.get_boxed_value(builder);
        let field_ptr;
        unsafe {
            field_ptr = builder.build_in_bounds_gep(
                boxed,
                &[
                    self.base.context.i64_type().const_int(0, false), // unboxing
                    self.base
                        .context
                        .i32_type()
                        .const_int((n as i32).try_into().unwrap(), false),
                ],
                "",
            );
        }
        let field = builder.build_load(field_ptr, "");
        assert_eq!(field.get_type(), self.get_nth_filed_boxed_type(n));
        field.into_pointer_value()
    }
}

struct EnumLayout<'ctx> {
    base: ObjectLayout<'ctx>,
    constructors: Vec<(String, Option<&'ctx dyn MemoryType<'ctx>>)>,
}

impl<'ctx> MemoryType<'ctx> for EnumLayout<'ctx> {
    fn get_common_type(&self) -> BasicTypeEnum<'ctx> {
        let header_typ = self.base.get_type();
        let tag_typ = self.base.context.i32_type();
        let i8_0_t = self
            .base
            .context
            .i8_type()
            .ptr_type(AddressSpace::Generic)
            .array_type(0);
        let typ = self
            .base
            .context
            .struct_type(&[header_typ, tag_typ.into(), i8_0_t.into()], true)
            .into();
        typ
    }

    fn get_type(&self) -> BasicTypeEnum<'ctx> {
        let header_typ = self.base.get_type();
        let tag_typ = self.base.context.i32_type();

        todo!()
    }
}


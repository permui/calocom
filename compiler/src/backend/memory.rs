use std::collections::HashMap;
use std::vec;

use crate::midend::type_context::{SingletonType, Type, TypeContext};
use crate::midend::*;

use super::runtime::*;
use inkwell::context::Context;
use inkwell::module::{self, Module};
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, PointerType};
use inkwell::AddressSpace;

pub struct MemoryLayoutContext<'ctx> {
    ty_ctx: TypeContext,
    llvm_ctx: &'ctx Context,
    type_name_map: HashMap<usize, String>,
    name_type_map: HashMap<String, BasicTypeEnum<'ctx>>,
    llvm_types: Vec<BasicTypeEnum<'ctx>>,
}

impl<'ctx> MemoryLayoutContext<'ctx> {
    fn initialize(&mut self, calocom_types: &[BasicTypeEnum<'ctx>]) {
        let i64_t = self.llvm_ctx.i64_type();
        let i32_t = self.llvm_ctx.i32_type();
        let i16_t = self.llvm_ctx.i16_type();
        let i8_t = self.llvm_ctx.i8_type();
        let i8_0_t = self.llvm_ctx.i8_type().array_type(0);
        let i8_p_t = self.llvm_ctx.i8_type().ptr_type(AddressSpace::Generic);

        // first pass
        for (idx, ty) in self.ty_ctx.types.iter().enumerate() {
            if SingletonType::is_singleton_type(idx) {
                self.llvm_types.push(calocom_types[idx])
            } else {
                match ty {
                    Type::Opaque(_) | Type::Reference(_) => {
                        // do not generate opaque struct type for opaque type and reference type
                        // they are aliases or references to other types
                        self.llvm_types.push(i32_t.as_basic_type_enum());
                    }
                    _ => {
                        let name = self.type_name_map.get(&idx).unwrap();
                        let opaque_struct = self.llvm_ctx.opaque_struct_type(name.as_str());
                        self.llvm_types.push(opaque_struct.as_basic_type_enum());
                        self.name_type_map
                            .insert(name.to_string(), opaque_struct.as_basic_type_enum());
                    }
                }
            }
        }
        // second pass
        let object_t = self.llvm_types[SingletonType::OBJECT];
        for (ty, (idx, llvm_ty)) in self
            .ty_ctx
            .types
            .iter()
            .zip(self.llvm_types.iter_mut().enumerate())
        {
            if !SingletonType::is_singleton_type(idx) {
                match ty {
                    Type::Tuple(x) => {
                        let mut fields = vec![object_t.as_basic_type_enum()];
                        for ty in x.as_ref().fields.iter() {
                            let name = self
                                .type_name_map
                                .get(&self.ty_ctx.get_idx_by_type(ty))
                                .unwrap();
                            let field_ty = self
                                .name_type_map
                                .get(name.as_str())
                                .unwrap()
                                .ptr_type(AddressSpace::Generic)
                                .as_basic_type_enum();
                            fields.push(field_ty);
                        }
                        llvm_ty.into_struct_type().set_body(&fields[..], true);
                    }
                    Type::Enum(_) => {
                        llvm_ty
                            .into_struct_type()
                            .set_body(&[object_t, i8_p_t.into()], true);
                    }
                    Type::Primitive(x) => match x.typ {
                        type_context::PrimitiveType::Object => {
                            llvm_ty.into_struct_type().set_body(
                                &[i64_t.into(), i8_t.into(), i8_t.into(), i16_t.into()],
                                true,
                            );
                        }
                        type_context::PrimitiveType::Str => {
                            llvm_ty
                                .into_struct_type()
                                .set_body(&[object_t, i32_t.into(), i8_0_t.into()], true);
                        }
                        type_context::PrimitiveType::Bool | type_context::PrimitiveType::Int32 => {
                            llvm_ty
                                .into_struct_type()
                                .set_body(&[object_t, i32_t.into()], true);
                        }
                        type_context::PrimitiveType::Unit => {
                            llvm_ty.into_struct_type().set_body(&[object_t], true);
                        }
                        type_context::PrimitiveType::CInt32 => {
                            *llvm_ty = self.llvm_ctx.i32_type().into();
                        }
                    },
                    Type::Opaque(x) => {
                        let name = x.alias.as_ref().right().unwrap();
                        let typ = self
                            .name_type_map
                            .get(name.as_str())
                            .unwrap()
                            .as_basic_type_enum();
                        *llvm_ty = typ;

                        let name = self.type_name_map.get(&idx).unwrap();
                        self.name_type_map.insert(name.to_string(), typ);
                    }
                    Type::Reference(x) => {
                        let name = x.refer.as_ref().right().unwrap();
                        let typ = self
                            .name_type_map
                            .get(name.as_str())
                            .unwrap()
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum();
                        *llvm_ty = typ;

                        let name = self.type_name_map.get(&idx).unwrap();
                        self.name_type_map.insert(name.to_string(), typ);
                    }
                }
            }
        }
    }

    pub fn new(
        ty_ctx: TypeContext,
        llvm_ctx: &'ctx Context,
        calocom_types: &[BasicTypeEnum<'ctx>],
    ) -> Self {
        let (ty_ctx, type_name_map) = ty_ctx.get_display_name_map();
        let mut ctx = MemoryLayoutContext {
            ty_ctx,
            llvm_ctx,
            type_name_map,
            llvm_types: vec![],
            name_type_map: HashMap::new(),
        };
        ctx.initialize(calocom_types);
        ctx
    }

    pub fn get_llvm_type_by_idx(&self, typ: usize) -> BasicTypeEnum<'ctx> {
        self.llvm_types[typ]
    }

    pub fn get_mir_type_idx(&self, typ: usize) -> Type {
        self.ty_ctx.get_type_by_idx(typ)
    }

    pub fn get_fn_type_of_basic_type_enum(
        typ: BasicTypeEnum<'ctx>,
        param_types: &[BasicMetadataTypeEnum<'ctx>],
        is_var_args: bool,
    ) -> FunctionType<'ctx> {
        match typ {
            BasicTypeEnum::ArrayType(x) => x.fn_type(param_types, is_var_args),
            BasicTypeEnum::FloatType(x) => x.fn_type(param_types, is_var_args),
            BasicTypeEnum::IntType(x) => x.fn_type(param_types, is_var_args),
            BasicTypeEnum::PointerType(x) => x.fn_type(param_types, is_var_args),
            BasicTypeEnum::StructType(x) => x.fn_type(param_types, is_var_args),
            BasicTypeEnum::VectorType(x) => x.fn_type(param_types, is_var_args),
        }
    }
}

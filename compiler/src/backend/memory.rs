use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::vec;

use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType};
use inkwell::AddressSpace;
use strum::IntoEnumIterator;

use crate::common::runtime::{CoreLibrary, RuntimeType};
use crate::common::type_context::*;

pub struct MemoryLayoutContext<'ctx> {
    ty_ctx: TypeContext,
    type_name_map: HashMap<TypeRef, String>,
    llvm_ctx: &'ctx Context,
    llvm_module: Rc<Module<'ctx>>,
    type_llvm_type_map: HashMap<TypeRef, BasicTypeEnum<'ctx>>,
}

impl<'ctx> MemoryLayoutContext<'ctx> {
    pub fn get_mir_type_context(&self) -> &TypeContext {
        &self.ty_ctx
    }

    pub fn get_mut_mir_type_context(&mut self) -> &mut TypeContext {
        &mut self.ty_ctx
    }

    fn initialize(&mut self) {
        let i8_p_t = self.llvm_ctx.i8_type().ptr_type(AddressSpace::Generic);

        for prim in Primitive::iter() {
            let ty_ref = self.ty_ctx.primitive_type(prim);
            self.type_llvm_type_map
                .insert(ty_ref, self.llvm_module.get_calocom_type(prim.into()));
        }

        let memo_prim: HashSet<_> = self.ty_ctx.primitive_types().iter().copied().collect();
        // first pass
        for (ty_ref, ty) in self.ty_ctx.types().iter() {
            if memo_prim.contains(&ty_ref) {
                continue;
            }

            match ty {
                Type::Opaque { .. } | Type::Primitive(_) => unreachable!(),
                Type::Reference { .. } => {
                    // do not generate opaque struct type for reference type
                    // now because it is a ptr to other type. Make it later.
                }
                Type::Callable {
                    kind,
                    ret_type: _,
                    parameters: _,
                } if !matches!(kind, CallKind::ClosureValue) => {
                    // do not generate opaque struct type callable type
                    // (kind: function, constructor) because they
                    // don't represent a bottom data type in the memory level
                }
                _ => {
                    let name = self.type_name_map.get(&ty_ref).unwrap();
                    let opaque_struct = self.llvm_ctx.opaque_struct_type(name.as_str());
                    self.type_llvm_type_map
                        .insert(ty_ref, opaque_struct.as_basic_type_enum());
                }
            }
        }

        // second pass
        let object_t = self.llvm_module.get_calocom_type(RuntimeType::Object);
        for (ty_ref, ty) in self.ty_ctx.types().iter() {
            if memo_prim.contains(&ty_ref) {
                continue;
            }
            match ty {
                Type::Tuple { fields: x } => {
                    let mut fields = vec![object_t.as_basic_type_enum()];
                    for ty in x.iter() {
                        let llvm_type = self.type_llvm_type_map.get(ty).unwrap();
                        let field_ty = llvm_type
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum();
                        fields.push(field_ty);
                    }
                    self.type_llvm_type_map
                        .get_mut(&ty_ref)
                        .unwrap()
                        .into_struct_type()
                        .set_body(&fields[..], true);
                }
                Type::Enum { .. } => {
                    self.type_llvm_type_map
                        .get_mut(&ty_ref)
                        .unwrap()
                        .into_struct_type()
                        .set_body(&[object_t, i8_p_t.into()], true);
                }
                Type::Primitive(_) | Type::Opaque { .. } => {
                    unreachable!()
                }
                Type::Reference { refer } => {
                    let referred_type = refer.as_ref().left().unwrap();
                    let referred_type = self.type_llvm_type_map.get(referred_type).unwrap();
                    self.type_llvm_type_map.insert(ty_ref, *referred_type);
                }
                Type::Array(elem) => {
                    let elem_ty = self
                        .type_llvm_type_map
                        .get(elem)
                        .unwrap()
                        .ptr_type(AddressSpace::Generic)
                        .as_basic_type_enum();

                    self.type_llvm_type_map
                        .get_mut(&ty_ref)
                        .unwrap()
                        .into_struct_type()
                        .set_body(
                            &[
                                self.llvm_module.get_calocom_type(RuntimeType::Array),
                                elem_ty,
                            ],
                            true,
                        );
                }
                Type::Callable {
                    kind,
                    ret_type,
                    parameters,
                } if matches!(kind, CallKind::ClosureValue) => {
                    let mut params_type: Vec<_> = parameters
                        .iter()
                        .map(|param| {
                            self.type_llvm_type_map
                                .get(param)
                                .unwrap()
                                .ptr_type(AddressSpace::Generic)
                                .into()
                        })
                        .collect();

                    params_type.insert(
                        0,
                        self.llvm_module
                            .get_calocom_type(RuntimeType::Object)
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum()
                            .into(),
                    );

                    let fn_ptr_type = self
                        .type_llvm_type_map
                        .get(ret_type)
                        .unwrap()
                        .ptr_type(AddressSpace::Generic)
                        .fn_type(&params_type, false)
                        .ptr_type(AddressSpace::Generic)
                        .as_basic_type_enum();

                    self.type_llvm_type_map
                        .get_mut(&ty_ref)
                        .unwrap()
                        .into_struct_type()
                        .set_body(
                            &[
                                self.llvm_module.get_calocom_type(RuntimeType::Closure),
                                fn_ptr_type,
                            ],
                            true,
                        );
                }
                _ => {}
            }
        }
    }

    pub fn new(
        ty_ctx: TypeContext,
        llvm_ctx: &'ctx Context,
        llvm_module: Rc<Module<'ctx>>,
    ) -> Self {
        let (ty_ctx, type_name_map) = ty_ctx.get_display_name_map();
        let mut ctx = MemoryLayoutContext {
            ty_ctx,
            type_name_map,
            llvm_ctx,
            llvm_module,
            type_llvm_type_map: HashMap::new(),
        };
        ctx.initialize();
        ctx
    }

    pub fn get_llvm_type(&self, typ: TypeRef) -> BasicTypeEnum<'ctx> {
        *self.type_llvm_type_map.get(&typ).unwrap()
    }

    pub fn get_mir_type(&self, typ: TypeRef) -> Type {
        self.ty_ctx.get_type_by_ref(typ)
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

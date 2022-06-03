use std::{collections::HashMap, path::Path, rc::Rc};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum},
    values::{
        BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallableValue, FunctionValue, IntValue,
        PointerValue,
    },
    AddressSpace, FloatPredicate, IntPredicate,
};
use slotmap::SlotMap;

use super::{memory::MemoryLayoutContext, name_mangling::Mangling};
use crate::{
    ast::{BinOp, Literal},
    common::{
        dump::Dump,
        name_context::NameContext,
        runtime::{insert_library_function, CoreLibrary, RuntimeType},
        type_context::{Primitive, TypeRef},
    },
    midend::middle_ir::{
        Block, BlockRef, FuncDef, Operand, OperandEnum, Terminator, Value, ValueEnum, VarDef,
        VarDefRef,
    },
    MiddleIR,
};

#[derive(Debug)]
pub struct FunctionEmissionState<'ctx, 'a> {
    var_map: HashMap<VarDefRef, (bool, PointerValue<'ctx>)>,
    block_map: HashMap<BlockRef, BasicBlock<'ctx>>,
    func: FunctionValue<'ctx>,
    alloca_block: BasicBlock<'ctx>,
    ret_value: PointerValue<'ctx>,
    var_slotmap: &'a SlotMap<VarDefRef, VarDef>,
}

pub struct CodeGen<'ctx, 'a> {
    context: &'ctx Context,
    module: Rc<Module<'ctx>>,
    memory_layout_ctx: MemoryLayoutContext<'ctx>,
    function_value_ctx: NameContext<FunctionValue<'ctx>>,
    builder: Builder<'ctx>,
    current_function: Option<FunctionEmissionState<'ctx, 'a>>,
}

impl<'ctx, 'a> CodeGen<'ctx, 'a> {
    pub fn module(&self) -> &Module<'ctx> {
        self.module.as_ref()
    }

    pub fn new(
        llvm_ctx: &'ctx Context,
        llvm_mod: Module<'ctx>,
        mir: &MiddleIR,
        path: &Path,
    ) -> Self {
        let module = llvm_mod;
        let builder = llvm_ctx.create_builder();
        let ty_ctx = mir.ty_ctx.clone();

        module.link_calocom_runtime_module(path);
        let module = Rc::new(module);
        let mem_layout_ctx = MemoryLayoutContext::new(ty_ctx, llvm_ctx, module.clone());

        CodeGen {
            context: llvm_ctx,
            module,
            memory_layout_ctx: mem_layout_ctx,
            function_value_ctx: Default::default(),
            builder,
            current_function: None,
        }
    }

    // create stack allocation
    fn emit_local_alloca(
        &mut self,
        slots: &SlotMap<VarDefRef, VarDef>,
        variables: &[VarDefRef],
        ptr_level: usize,
    ) {
        CodeGen::set_insert_position_before_terminator(
            &self.builder,
            &self.current_function.as_ref().unwrap().alloca_block,
        );
        for var_ref in variables.iter().copied() {
            let var = slots.get(var_ref).unwrap();
            let mut typ = self.memory_layout_ctx.get_llvm_type(var.typ);
            assert!((0..=2).contains(&ptr_level));
            for _ in 0..ptr_level {
                typ = typ.ptr_type(AddressSpace::Generic).as_basic_type_enum();
            }
            let stack_slot = self
                .builder
                .build_alloca(dbg!(typ), dbg!(var.name.as_str()));
            self.current_function
                .as_mut()
                .unwrap()
                .var_map
                .insert(var_ref, (ptr_level == 2, stack_slot));
        }
    }

    // set the insert position to the last non-terminator instruction
    fn set_insert_position_before_terminator(builder: &Builder, block: &BasicBlock<'ctx>) {
        if let Some(terminator) = block.get_terminator() {
            builder.position_before(&terminator);
        } else {
            builder.position_at_end(*block);
        }
    }

    // create all basic blocks but not fill the instructions
    fn emit_basic_blocks(
        ctx: &'ctx Context,
        func: FunctionValue<'ctx>,
        blocks: &SlotMap<BlockRef, Block>,
    ) -> (
        HashMap<BlockRef, BasicBlock<'ctx>>,
        Option<BasicBlock<'ctx>>,
    ) {
        let mut map = HashMap::new();
        let mut entry = None;

        for (block_ref, block) in blocks {
            let name = block.name.clone();
            let bb = ctx.append_basic_block(func, name.as_str());
            map.insert(block_ref, bb);
            if name == "entry" {
                entry = Some(bb);
            }
        }

        (map, entry)
    }

    fn emit_fn_declaration(&mut self, mir_func: &'a FuncDef) {
        let FuncDef {
            name,
            blocks: _,
            variables,
            params,
            captured: _,
            locals: _,
            temporaries: _,
            obj_reference: _,
            unwrapped: _,
            return_value,
            entry_block: _,
            return_block: _,
            panic_block: _,
        } = mir_func;

        let mem_ctx = &self.memory_layout_ctx;

        // get the llvm type of return value
        let ret_var_ref = *return_value.as_ref().unwrap();
        let ret_var = variables.get(ret_var_ref).unwrap();
        let ret_type_ref = ret_var.typ;
        let ret_llvm_type = mem_ctx
            .get_llvm_type(ret_type_ref)
            .ptr_type(AddressSpace::Generic);

        // get the llvm type of parameters
        let mut params_llvm_type: Vec<BasicMetadataTypeEnum<'ctx>> = vec![];
        let mut params_type_ref = vec![];
        for var_ref in params.iter() {
            let param_var = variables.get(*var_ref).unwrap();
            let param_type_ref = param_var.typ;
            let typ = mem_ctx
                .get_llvm_type(param_var.typ)
                .ptr_type(AddressSpace::Generic);
            params_llvm_type.push(typ.into());
            params_type_ref.push(param_type_ref);
        }

        // get the llvm type of function
        let fn_type = MemoryLayoutContext::get_fn_type_of_basic_type_enum(
            ret_llvm_type.into(),
            &params_llvm_type,
            false,
        );

        // generate mangled name
        let ty_ctx = mem_ctx.get_mir_type_context();
        let decorated_name = ty_ctx.get_mangled_polymorphic_function_name(
            &[name.to_string()].as_slice(),
            ret_type_ref,
            &params_type_ref,
        );

        // create llvm function value
        let func = self
            .module
            .get_function(decorated_name.as_str())
            .unwrap_or_else(|| {
                self.module
                    .add_function(decorated_name.as_str(), fn_type, None)
            });

        // insert to name context
        self.function_value_ctx
            .insert_symbol(name.to_string(), func)
            .and_then(|_| -> Option<()> { panic!("duplicate function value") });
    }

    fn emit_fn(&mut self, mir_func: &'a FuncDef) {
        let FuncDef {
            name,
            blocks,
            variables,
            params,
            captured,
            locals,
            temporaries,
            obj_reference,
            unwrapped,
            return_value,
            entry_block: _,
            return_block: _,
            panic_block: _,
        } = mir_func;

        let mem_ctx = &self.memory_layout_ctx;

        // get the llvm type of return value
        let ret_var_ref = *return_value.as_ref().unwrap();
        let ret_var = variables.get(ret_var_ref).unwrap();
        let ret_type_ref = ret_var.typ;
        let ret_llvm_type = mem_ctx
            .get_llvm_type(ret_type_ref)
            .ptr_type(AddressSpace::Generic);

        // get the llvm type of parameters
        let mut params_llvm_type: Vec<BasicMetadataTypeEnum<'ctx>> = vec![];
        let mut params_type_ref = vec![];
        for var_ref in params.iter() {
            let param_var = variables.get(*var_ref).unwrap();
            let param_type_ref = param_var.typ;
            let typ = mem_ctx
                .get_llvm_type(param_var.typ)
                .ptr_type(AddressSpace::Generic);
            params_llvm_type.push(typ.into());
            params_type_ref.push(param_type_ref);
        }

        // generate mangled name
        let ty_ctx = mem_ctx.get_mir_type_context();
        let decorated_name = ty_ctx.get_mangled_polymorphic_function_name(
            &[name.to_string()].as_slice(),
            ret_type_ref,
            &params_type_ref,
        );

        // create llvm function value
        let func = self
            .module
            .get_function(decorated_name.as_str())
            .unwrap_or_else(|| unreachable!());

        // create all basic blocks and alloca block
        let alloca_block = self.context.append_basic_block(func, "alloca");
        CodeGen::set_insert_position_before_terminator(&self.builder, &alloca_block);
        let (block_map, entry_block) = CodeGen::emit_basic_blocks(self.context, func, blocks);

        // build the alloca of return value and insert it to map
        let mut var_map = HashMap::new();
        let ret_ptr = self.builder.build_alloca(ret_llvm_type, "ret.var.ptr");
        var_map.insert(ret_var_ref, (false, ret_ptr));

        self.current_function = Some(FunctionEmissionState {
            var_map,
            block_map,
            func,
            alloca_block,
            ret_value: ret_ptr,
            var_slotmap: variables,
        });

        self.emit_local_alloca(variables, captured, 1);
        self.emit_local_alloca(variables, params, 1);
        self.emit_local_alloca(variables, locals, 1);
        self.emit_local_alloca(variables, temporaries, 1);
        self.emit_local_alloca(variables, obj_reference, 2);
        self.emit_local_alloca(variables, unwrapped, 0);

        // store the arguments into local variables
        self.emit_arguments_store(params);
        self.builder
            .build_unconditional_branch(entry_block.unwrap());

        self.emit_all_stmts(blocks);
        self.emit_basic_block_terminators(blocks);
    }

    fn emit_all_stmts(&mut self, blocks: &SlotMap<BlockRef, Block>) {
        let block_map = &self.current_function.as_ref().unwrap().block_map;
        for (bb_ref, bb) in blocks {
            let llvm_bb = block_map.get(&bb_ref).unwrap();
            self.emit_stmts(bb, llvm_bb);
        }
    }

    fn emit_stmts(&self, block: &Block, llvm_block: &BasicBlock) {
        CodeGen::set_insert_position_before_terminator(&self.builder, llvm_block);

        for stmt in &block.stmts {
            let rhs = stmt.right.as_ref().unwrap();
            let rhs_ret_ref = matches!(&rhs.val, ValueEnum::Index(_, _));
            let rhs = self.emit_value(rhs);
            if let Some(left) = &stmt.left {
                let ptr = self.emit_stack_slot(*left, rhs_ret_ref);
                self.builder
                    .build_store(dbg!(ptr.into_pointer_value()), dbg!(rhs));
            }
        }
    }

    fn emit_variable(&self, var: VarDefRef) -> BasicValueEnum<'ctx> {
        let &(is_ref, ptr) = self
            .current_function
            .as_ref()
            .unwrap()
            .var_map
            .get(&var)
            .unwrap_or_else(|| panic!("variable map doesn't contains the var"));
        let mut bv: BasicValueEnum = self.builder.build_load(ptr, "");
        if is_ref {
            bv = self.builder.build_load(bv.into_pointer_value(), "");
        }
        bv
    }

    fn emit_stack_slot(&self, var: VarDefRef, do_not_deref: bool) -> BasicValueEnum<'ctx> {
        let &(is_ref, ptr) = self
            .current_function
            .as_ref()
            .unwrap()
            .var_map
            .get(&var)
            .unwrap_or_else(|| panic!("variable map doesn't contains the var"));
        let mut bv: BasicValueEnum = ptr.into();
        if is_ref && !do_not_deref {
            bv = self.builder.build_load(bv.into_pointer_value(), "");
        }
        bv
    }

    fn emit_operand(&self, operand: &Operand) -> BasicValueEnum<'ctx> {
        let Operand { val, .. } = operand;
        match val.as_ref() {
            OperandEnum::Imm(_) => {
                panic!("not allowed to make boxed immediate value")
            }
            OperandEnum::Literal(lit) => self.emit_literal_value(true, lit),
            OperandEnum::Var(var) => self.emit_variable(*var),
        }
    }

    fn emit_unboxed_operand(&self, operand: &Operand) -> BasicValueEnum<'ctx> {
        let Operand { val, .. } = operand;
        match val.as_ref() {
            OperandEnum::Imm(i) => self
                .context
                .i32_type()
                .const_int(*i as u64, false)
                .as_basic_value_enum(),
            OperandEnum::Literal(lit) => self.emit_literal_value(false, lit),
            OperandEnum::Var(var) => {
                let llvm_var = self.emit_variable(*var);
                let ty_ctx = self.memory_layout_ctx.get_mir_type_context();

                let var_def = self
                    .current_function
                    .as_ref()
                    .unwrap()
                    .var_slotmap
                    .get(*var)
                    .unwrap();

                let typ = var_def.typ;
                let res = if typ == ty_ctx.primitive_type(Primitive::Int32) {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_extract_i32(),
                            &[llvm_var.into(), self.context.i32_type().const_zero().into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else if typ == ty_ctx.primitive_type(Primitive::Float64) {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_extract_f64(),
                            &[llvm_var.into(), self.context.f64_type().const_zero().into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else if typ == ty_ctx.primitive_type(Primitive::Bool) {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_extract_bool(),
                            &[
                                llvm_var.into(),
                                self.context.bool_type().const_zero().into(),
                            ],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else if typ == ty_ctx.primitive_type(Primitive::CInt32) {
                    llvm_var
                } else {
                    panic!("can't generate unboxed value for this")
                };

                res
            }
        }
    }

    fn emit_cast_closure_value_to_base(&self, closure: BasicValueEnum<'ctx>) -> PointerValue<'ctx> {
        self.emit_cast_value_pointer(closure, self.module.get_calocom_type(RuntimeType::Closure))
    }

    fn emit_cast_object_value_to_base(&self, object: BasicValueEnum<'ctx>) -> PointerValue<'ctx> {
        self.emit_cast_value_pointer(object, self.module.get_calocom_type(RuntimeType::Object))
    }

    fn emit_cast_enum_value_to_base(&self, object: BasicValueEnum<'ctx>) -> PointerValue<'ctx> {
        self.emit_cast_value_pointer(object, self.module.get_calocom_type(RuntimeType::Enum))
    }

    fn emit_cast_tuple_value_to_base(&self, object: BasicValueEnum<'ctx>) -> PointerValue<'ctx> {
        self.emit_cast_value_pointer(object, self.module.get_calocom_type(RuntimeType::Tuple))
    }

    fn emit_cast_value_pointer(
        &self,
        object: BasicValueEnum<'ctx>,
        target: BasicTypeEnum<'ctx>,
    ) -> PointerValue<'ctx> {
        if !object.is_pointer_value() {
            panic!("not a pointer to closure");
        }
        let ptr = object.into_pointer_value();
        let converted =
            self.builder
                .build_pointer_cast(ptr, target.ptr_type(AddressSpace::Generic), "");
        converted
    }

    fn emit_literal_value(&self, need_boxing: bool, literal: &Literal) -> BasicValueEnum<'ctx> {
        match literal {
            Literal::Int(i) => {
                let i = self
                    .context
                    .i32_type()
                    .const_int(*i as u64, false)
                    .as_basic_value_enum();
                if need_boxing {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_alloc_i32_literal(),
                            &[i.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    i
                }
            }
            Literal::Str(s) => {
                let str = self
                    .builder
                    .build_global_string_ptr(s.as_str(), "")
                    .as_pointer_value()
                    .as_basic_value_enum();
                if need_boxing {
                    let len = self
                        .context
                        .i64_type()
                        .const_int(s.as_bytes().len() as u64, false)
                        .into();
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_alloc_string_literal(),
                            &[len, str.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    str
                }
            }
            Literal::Bool(b) => {
                if need_boxing {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_alloc_bool_literal(),
                            &[self
                                .context
                                .bool_type()
                                .const_int(*b as u64, false)
                                .as_basic_value_enum()
                                .into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    self.context
                        .i32_type()
                        .const_int(*b as u64, false)
                        .as_basic_value_enum()
                }
            }
            Literal::Float(f) => {
                let f = self
                    .context
                    .f64_type()
                    .const_float(*f)
                    .as_basic_value_enum();
                if need_boxing {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_alloc_f64_literal(),
                            &[f.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    f
                }
            }
            Literal::Unit => {
                if need_boxing {
                    self.builder
                        .build_call(self.module.get_runtime_function_alloc_unit(), &[], "")
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    // can't produce a unboxed unit value
                    unreachable!()
                }
            }
        }
    }

    fn load_closure_fn(&self, closure: BasicValueEnum<'ctx>) -> PointerValue<'ctx> {
        if !closure.is_pointer_value() {
            panic!("not a pointer to closure");
        }
        let fn_ptr = self
            .builder
            .build_struct_gep(closure.into_pointer_value(), 1, "")
            .expect("not a struct type");
        let fn_ptr = self.builder.build_load(fn_ptr, "");
        if !fn_ptr.is_pointer_value() {
            panic!("not a function pointer");
        }
        fn_ptr.into_pointer_value()
    }

    fn store_closure_fn(&self, closure: PointerValue<'ctx>, closure_fn: FunctionValue<'ctx>) {
        let fn_ptr = self
            .builder
            .build_struct_gep(closure, 1, "")
            .expect("not a struct type");
        self.builder.build_store(
            fn_ptr,
            closure_fn
                .as_global_value()
                .as_pointer_value()
                .as_basic_value_enum(),
        );
    }

    fn emit_boxed_bool(&self, value: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.builder
            .build_call(
                self.module.get_runtime_function_alloc_bool_literal(),
                &[value.into()],
                "",
            )
            .try_as_basic_value()
            .left()
            .unwrap()
    }

    fn emit_boxed_i32(&self, value: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.builder
            .build_call(
                self.module.get_runtime_function_alloc_i32_literal(),
                &[value.into()],
                "",
            )
            .try_as_basic_value()
            .left()
            .unwrap()
    }

    fn emit_boxed_f64(&self, value: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        self.builder
            .build_call(
                self.module.get_runtime_function_alloc_f64_literal(),
                &[value.into()],
                "",
            )
            .try_as_basic_value()
            .left()
            .unwrap()
    }

    fn convert_to_boolean(&self, value: IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        self.builder
            .build_int_compare(
                IntPredicate::NE,
                value,
                value.get_type().const_int(0, false),
                "",
            )
            .as_basic_value_enum()
    }

    fn extend_to_i32(&self, value: IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        self.builder
            .build_int_z_extend(value, self.context.i32_type(), "")
            .as_basic_value_enum()
    }

    fn emit_logical_op(
        &self,
        op: BinOp,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        use crate::ast::BinOp::*;
        self.emit_boxed_bool(
            self.convert_to_boolean(match op {
                And => self
                    .builder
                    .build_and(lhs.into_int_value(), rhs.into_int_value(), ""),
                Or => self
                    .builder
                    .build_or(lhs.into_int_value(), rhs.into_int_value(), ""),
                _ => unreachable!(),
            }),
        )
    }

    fn emit_relational_op(
        &self,
        op: BinOp,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        use crate::ast::BinOp::*;
        self.emit_boxed_bool(if lhs.is_float_value() {
            match op {
                Eq => self
                    .builder
                    .build_float_compare(
                        FloatPredicate::OEQ,
                        lhs.into_float_value(),
                        rhs.into_float_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Ne => self
                    .builder
                    .build_float_compare(
                        FloatPredicate::UNE,
                        lhs.into_float_value(),
                        rhs.into_float_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Ge => self
                    .builder
                    .build_float_compare(
                        FloatPredicate::OGE,
                        lhs.into_float_value(),
                        rhs.into_float_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Le => self
                    .builder
                    .build_float_compare(
                        FloatPredicate::OLE,
                        lhs.into_float_value(),
                        rhs.into_float_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Gt => self
                    .builder
                    .build_float_compare(
                        FloatPredicate::OGT,
                        lhs.into_float_value(),
                        rhs.into_float_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Lt => self
                    .builder
                    .build_float_compare(
                        FloatPredicate::OLT,
                        lhs.into_float_value(),
                        rhs.into_float_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                _ => unreachable!(),
            }
        } else if lhs.is_int_value() {
            match op {
                Eq => self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Ne => self
                    .builder
                    .build_int_compare(
                        IntPredicate::NE,
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Ge => self
                    .builder
                    .build_int_compare(
                        IntPredicate::SGE,
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Le => self
                    .builder
                    .build_int_compare(
                        IntPredicate::SLE,
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Gt => self
                    .builder
                    .build_int_compare(
                        IntPredicate::SGT,
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                Lt => self
                    .builder
                    .build_int_compare(
                        IntPredicate::SLT,
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "",
                    )
                    .as_basic_value_enum(),
                _ => unreachable!(),
            }
        } else {
            panic!("can't apply relational operation in such type");
        })
    }

    fn emit_test_string_equality(
        &self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
    ) -> BasicValueEnum<'ctx> {
        let lhs = self.emit_operand(lhs);
        let rhs = self.emit_operand(rhs);
        self.emit_boxed_bool(
            self.builder
                .build_call(
                    self.module.get_runtime_function_compare_string(),
                    &[
                        lhs.into(),
                        rhs.into(),
                        self.context
                            .bool_type()
                            .const_int(
                                match op {
                                    crate::ast::BinOp::Eq => 1,
                                    crate::ast::BinOp::Ne => 0,
                                    _ => unreachable!(),
                                } as u64,
                                false,
                            )
                            .into(),
                    ],
                    "",
                )
                .try_as_basic_value()
                .left()
                .unwrap()
                .into_int_value()
                .as_basic_value_enum(),
        )
    }

    fn emit_arithmetic_op(
        &self,
        op: BinOp,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        use crate::ast::BinOp::*;
        if lhs.is_float_value() {
            self.emit_boxed_f64(match op {
                Plus => self
                    .builder
                    .build_float_add(lhs.into_float_value(), rhs.into_float_value(), "")
                    .as_basic_value_enum(),
                Sub => self
                    .builder
                    .build_float_sub(lhs.into_float_value(), rhs.into_float_value(), "")
                    .as_basic_value_enum(),
                Mul => self
                    .builder
                    .build_float_mul(lhs.into_float_value(), rhs.into_float_value(), "")
                    .as_basic_value_enum(),
                Div => self
                    .builder
                    .build_float_div(lhs.into_float_value(), rhs.into_float_value(), "")
                    .as_basic_value_enum(),
                Mod => self
                    .builder
                    .build_float_rem(lhs.into_float_value(), rhs.into_float_value(), "")
                    .as_basic_value_enum(),
                _ => unreachable!(),
            })
        } else if lhs.is_int_value() {
            self.emit_boxed_i32(match op {
                Plus => self
                    .builder
                    .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "")
                    .as_basic_value_enum(),
                Sub => self
                    .builder
                    .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "")
                    .as_basic_value_enum(),
                Mul => self
                    .builder
                    .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "")
                    .as_basic_value_enum(),
                Div => self
                    .builder
                    .build_int_signed_div(lhs.into_int_value(), rhs.into_int_value(), "")
                    .as_basic_value_enum(),
                Mod => self
                    .builder
                    .build_int_signed_rem(lhs.into_int_value(), rhs.into_int_value(), "")
                    .as_basic_value_enum(),
                _ => unreachable!(),
            })
        } else {
            unreachable!()
        }
    }

    fn emit_construct_tuple(&self, fields: &[Operand]) -> BasicValueEnum<'ctx> {
        let args: Vec<_> = fields
            .iter()
            .map(|arg| {
                self.emit_cast_object_value_to_base(self.emit_operand(arg))
                    .into()
            })
            .collect();

        let function = match args.len() {
            0 => panic!("can't make a tuple without any fields"),
            1 => self.module.get_runtime_function_construct_tuple_1(),
            2 => self.module.get_runtime_function_construct_tuple_2(),
            3 => self.module.get_runtime_function_construct_tuple_3(),
            4 => self.module.get_runtime_function_construct_tuple_4(),
            5 => self.module.get_runtime_function_construct_tuple_5(),
            6 => self.module.get_runtime_function_construct_tuple_6(),
            7 => self.module.get_runtime_function_construct_tuple_7(),
            8 => self.module.get_runtime_function_construct_tuple_8(),
            _ => panic!("too many fields "),
        };

        self.builder
            .build_call(function, &args, "")
            .try_as_basic_value()
            .left()
            .unwrap()
    }

    fn convert_number_type(
        &self,
        source: BasicValueEnum<'ctx>,
        source_type: TypeRef,
        target_type: TypeRef,
    ) -> BasicValueEnum<'ctx> {
        let ty_ctx = self.memory_layout_ctx.get_mir_type_context();
        if target_type == ty_ctx.primitive_type(Primitive::Object)
            && source_type != ty_ctx.primitive_type(Primitive::CInt32)
        {
            return self
                .builder
                .build_pointer_cast(
                    source.into_pointer_value(),
                    self.module
                        .get_calocom_type(RuntimeType::Object)
                        .ptr_type(AddressSpace::Generic),
                    "",
                )
                .as_basic_value_enum();
        }

        if target_type == ty_ctx.primitive_type(Primitive::Float64)
            && source_type == ty_ctx.primitive_type(Primitive::Int32)
        {
            return self
                .builder
                .build_call(
                    self.module.get_runtime_function_i32_to_f64(),
                    &[source.into()],
                    "",
                )
                .try_as_basic_value()
                .left()
                .unwrap();
        }

        if target_type == ty_ctx.primitive_type(Primitive::Int32)
            && source_type == ty_ctx.primitive_type(Primitive::Float64)
        {
            return self
                .builder
                .build_call(
                    self.module.get_runtime_function_f64_to_i32(),
                    &[source.into()],
                    "",
                )
                .try_as_basic_value()
                .left()
                .unwrap();
        }

        panic!(
            "not supported type conversion: {} to {}",
            (ty_ctx, source_type).dump_string(),
            (ty_ctx, target_type).dump_string()
        )
    }

    fn emit_value(&self, value: &Value) -> BasicValueEnum<'ctx> {
        let Value { typ, val } = value;
        use crate::midend::middle_ir::ValueEnum::*;
        match val {
            Call(path, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.emit_operand(arg).into())
                    .collect();
                let function = self
                    .function_value_ctx
                    .find_symbol(path)
                    .unwrap_or_else(|| panic!("unable to find function {}", path.join(".")));
                // NOTE: void function not allowed in calocom, so choose the left
                self.emit_cast_value_pointer(
                    self.builder
                        .build_call(function, &args, "")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into()
            }
            ExtCall(path, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.emit_operand(arg).into())
                    .collect();
                let function = self
                    .function_value_ctx
                    .find_symbol(path)
                    .unwrap_or_else(|| panic!("unable to find function {}", path.join(".")));
                // NOTE: void function not allowed in calocom, so choose the left
                self.emit_cast_value_pointer(
                    self.builder
                        .build_call(function, &args, "")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into()
            }
            ExtractClosureCapture(var, index) => {
                let closure = self.emit_variable(*var);
                let closure = self.emit_cast_closure_value_to_base(closure);
                let index = self.context.i32_type().const_int(*index as u64, false);

                let function = self.module.get_runtime_function_extract_closure_capture();
                self.emit_cast_value_pointer(
                    self.builder
                        .build_call(function, &[closure.into(), index.into()], "")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into()
            }
            ClosureCall(operand, args) => {
                let closure_self = self.emit_operand(operand);
                let fn_ptr = self.load_closure_fn(closure_self);

                let mut new_args = vec![self.emit_cast_object_value_to_base(closure_self).into()];
                new_args.extend(
                    args.iter().map(|arg| -> BasicMetadataValueEnum<'ctx> {
                        self.emit_operand(arg).into()
                    }),
                );

                self.builder
                    .build_call(
                        CallableValue::try_from(fn_ptr).expect("not a callable function pointer"),
                        &new_args,
                        "",
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            MakeClosure { path, capture } => {
                let closure_fn = self
                    .function_value_ctx
                    .find_symbol(path)
                    .unwrap_or_else(|| panic!("can't find {}", path.join(".")));

                let captured_array = self.builder.build_alloca(
                    self.module
                        .get_calocom_type(RuntimeType::Object)
                        .ptr_type(AddressSpace::Generic)
                        .array_type(capture.len() as u32),
                    "",
                );

                for (idx, var) in capture.iter().enumerate() {
                    let val = self.emit_operand(var);
                    let gep = unsafe {
                        self.builder.build_in_bounds_gep(
                            captured_array,
                            &[
                                self.context.i32_type().const_int(0, false),
                                self.context.i32_type().const_int(idx as u64, false),
                            ],
                            "",
                        )
                    };
                    self.builder
                        .build_store(gep, self.emit_cast_object_value_to_base(val));
                }

                let captured = self.builder.build_pointer_cast(
                    captured_array,
                    self.module
                        .get_calocom_type(RuntimeType::Object)
                        .ptr_type(AddressSpace::Generic)
                        .array_type(0)
                        .ptr_type(AddressSpace::Generic),
                    "",
                );

                let closure_ptr = self
                    .builder
                    .build_call(
                        self.module.get_runtime_function_create_closure(),
                        &[
                            captured.into(),
                            self.context
                                .i32_type()
                                .const_int(capture.len() as u64, false)
                                .into(),
                        ],
                        "",
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_pointer_value();

                let closure_ptr = self.builder.build_pointer_cast(
                    closure_ptr,
                    self.memory_layout_ctx
                        .get_llvm_type(*typ)
                        .ptr_type(AddressSpace::Generic),
                    "",
                );

                self.store_closure_fn(closure_ptr, closure_fn);

                closure_ptr.as_basic_value_enum()
            }
            BinaryOp(op, lhs, rhs) => {
                let t1 = lhs.typ;
                let t2 = rhs.typ;

                if t1 != t2 {
                    panic!(
                        "{} != {}",
                        (self.memory_layout_ctx.get_mir_type_context(), t1).dump_string(),
                        (self.memory_layout_ctx.get_mir_type_context(), t2).dump_string(),
                    );
                }

                use crate::ast::BinOp::*;
                if t1
                    == self
                        .memory_layout_ctx
                        .get_mir_type_context()
                        .primitive_type(Primitive::Str)
                {
                    assert!(matches!(op, Eq | Ne));
                    return self.emit_test_string_equality(*op, lhs, rhs);
                }

                let lhs_res = self.emit_unboxed_operand(lhs);
                let rhs_res = self.emit_unboxed_operand(rhs);
                match op {
                    Or | And => self.emit_logical_op(*op, lhs_res, rhs_res),
                    Le | Ge | Lt | Gt | Eq | Ne => self.emit_relational_op(*op, lhs_res, rhs_res),
                    Plus | Sub | Mul | Div | Mod => self.emit_arithmetic_op(*op, lhs_res, rhs_res),
                }
            }
            UnaryOp(op, expr) => {
                let expr = self.emit_unboxed_operand(expr);
                use crate::ast::UnaryOp::*;
                match op {
                    Not => {
                        if expr.is_int_value() {
                            self.emit_boxed_bool(
                                self.builder
                                    .build_not(expr.into_int_value(), "")
                                    .as_basic_value_enum(),
                            )
                        } else {
                            unreachable!()
                        }
                    }
                    Positive => expr,
                    Negative => {
                        if expr.is_float_value() {
                            self.emit_boxed_f64(
                                self.builder
                                    .build_float_neg(expr.into_float_value(), "")
                                    .as_basic_value_enum(),
                            )
                        } else if expr.is_int_value() {
                            self.emit_boxed_i32(
                                self.builder
                                    .build_int_neg(expr.into_int_value(), "")
                                    .as_basic_value_enum(),
                            )
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
            MakeTuple(args) => self
                .emit_cast_value_pointer(
                    self.emit_construct_tuple(args),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into(),
            Construct(discriminant, args) => self
                .emit_cast_value_pointer(
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_construct_enum(),
                            &[
                                self.context
                                    .i32_type()
                                    .const_int(*discriminant as u64, false)
                                    .into(),
                                if args.is_empty() {
                                    self.module
                                        .get_calocom_type(RuntimeType::Object)
                                        .ptr_type(AddressSpace::Generic)
                                        .const_null()
                                        .as_basic_value_enum()
                                        .into()
                                } else {
                                    self.emit_cast_object_value_to_base(
                                        self.emit_construct_tuple(args),
                                    )
                                    .into()
                                },
                            ],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into(),
            Intrinsic(name, args) => {
                if *name == "convert" {
                    assert!(args.len() == 1);
                    let src = self.emit_operand(&args[0]);

                    let src_type = args[0].typ;
                    let target_type = *typ;

                    self.convert_number_type(src, src_type, target_type)
                } else {
                    panic!("intrinsic {} not exist", name);
                }
            }
            Index(array, index) => {
                let array = self.emit_cast_value_pointer(
                    self.emit_operand(array),
                    self.module.get_calocom_type(RuntimeType::Array),
                );
                let array_index = self.emit_operand(index);

                // NOTICE: we return a 2-level pointer here
                self.emit_cast_value_pointer(
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_array_index(),
                            &[array.into(), array_index.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                        .as_basic_value_enum(),
                    self.memory_layout_ctx
                        .get_llvm_type(*typ)
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                )
                .into()
            }
            Operand(operand) => self.emit_operand(operand),
            UnboxedOperand(operand) => self.emit_unboxed_operand(operand),
            ExtractTupleField(operand, index) => {
                let tuple = self.emit_operand(operand);
                let tuple = self.emit_cast_tuple_value_to_base(tuple);

                self.emit_cast_value_pointer(
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_extract_tuple_field(),
                            &[
                                tuple.into(),
                                self.context
                                    .i32_type()
                                    .const_int(*index as u64, false)
                                    .into(),
                            ],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into()
            }
            ExtractEnumField(discriminant, operand, index) => {
                let obj = self.emit_operand(operand);
                let obj = self.emit_cast_enum_value_to_base(obj);

                self.emit_cast_value_pointer(
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_extract_enum_field(),
                            &[
                                obj.into(),
                                self.context
                                    .i32_type()
                                    .const_int(*discriminant as u64, false)
                                    .into(),
                                self.context
                                    .i32_type()
                                    .const_int(*index as u64, false)
                                    .into(),
                            ],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    self.memory_layout_ctx.get_llvm_type(*typ),
                )
                .into()
            }
            ExtractEnumTag(obj) => {
                let obj = self.emit_operand(obj);
                let obj = self.emit_cast_enum_value_to_base(obj);

                self.builder
                    .build_call(
                        self.module.get_runtime_function_extract_enum_tag(),
                        &[obj.into()],
                        "",
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .as_basic_value_enum()
            }
            CombineByFoldWithAnd1(args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| -> BasicMetadataValueEnum<'ctx> {
                        self.convert_to_boolean(self.emit_unboxed_operand(arg).into_int_value())
                            .into()
                    })
                    .collect();

                let result = args
                    .iter()
                    .fold(self.context.bool_type().const_int(1, false), |a, b| {
                        self.builder.build_and(a, b.into_int_value(), "")
                    });

                self.extend_to_i32(self.convert_to_boolean(result).into_int_value())
            }
            UnboxBool(operand) => {
                let b = self.emit_unboxed_operand(operand);
                self.extend_to_i32(b.into_int_value())
            }
            UnboxInt32(operand) => self.emit_unboxed_operand(operand),
            CompareStr(var, lit) => {
                let str_var = self.emit_operand(var);
                let str_lit = self.emit_literal_value(false, lit);
                let Literal::Str(s) = lit else { unreachable!() };

                self.builder
                    .build_call(
                        self.module.get_runtime_function_compare_string_with_cstr(),
                        &[
                            str_var.into(),
                            str_lit.into(),
                            self.context
                                .i32_type()
                                .const_int(s.len() as u64, false)
                                .into(),
                        ],
                        "",
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            CompareCInt32(var, imm) => {
                let var = self.emit_unboxed_operand(var);

                self.extend_to_i32(self.builder.build_int_compare(
                    IntPredicate::EQ,
                    var.into_int_value(),
                    self.context.i32_type().const_int(*imm as u64, false),
                    "",
                ))
            }
            IncreaseIndVar(var) => {
                let typ = var.typ;
                let var = self.emit_operand(var);

                if typ
                    == self
                        .memory_layout_ctx
                        .get_mir_type_context()
                        .primitive_type(Primitive::Int32)
                {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_increase_i32(),
                            &[var.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else if typ
                    == self
                        .memory_layout_ctx
                        .get_mir_type_context()
                        .primitive_type(Primitive::Float64)
                {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_increase_f64(),
                            &[var.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn emit_arguments_store(&mut self, params: &[VarDefRef]) {
        let func = self.current_function.as_ref().unwrap().func;
        for (idx, var) in params.iter().enumerate() {
            let stack_slot = self.emit_stack_slot(*var, false);
            let arg = func.get_nth_param(idx as u32).expect("expect an argument");
            self.builder
                .build_store(dbg!(stack_slot.into_pointer_value()), dbg!(arg));
        }
    }

    fn emit_basic_block_terminators(&self, blocks: &SlotMap<BlockRef, Block>) {
        let state = self.current_function.as_ref().unwrap();
        let ret_var_ptr = state.ret_value;
        let block_map = &state.block_map;

        for (block_ref, block) in blocks.iter() {
            let llvm_block = block_map.get(&block_ref).unwrap();
            self.builder.position_at_end(*llvm_block);

            match &block.terminator {
                Terminator::Branch(cond, then, or) => {
                    let cond = self.emit_unboxed_operand(cond);
                    let cond = self.convert_to_boolean(cond.into_int_value());
                    self.builder.build_conditional_branch(
                        cond.into_int_value(),
                        *block_map.get(then).unwrap(),
                        *block_map.get(or).unwrap(),
                    );
                }
                Terminator::Select(cond, choices, other) => {
                    let cond = self.emit_variable(*cond);
                    let choices: Vec<_> = choices
                        .iter()
                        .map(|(i, block_ref)| {
                            (
                                self.context.i32_type().const_int(*i as u64, false),
                                *block_map.get(block_ref).unwrap(),
                            )
                        })
                        .collect();
                    self.builder.build_switch(
                        cond.into_int_value(),
                        *block_map.get(other).unwrap(),
                        &choices,
                    );
                }
                Terminator::Jump(x) => {
                    let target = block_map.get(x).unwrap();
                    self.builder.build_unconditional_branch(*target);
                }
                Terminator::Return => {
                    let ret_var = self.builder.build_load(ret_var_ptr, "ret.var");
                    self.builder.build_return(Some(&ret_var));
                }
                Terminator::Panic => {
                    self.builder.build_call(
                        self.module.get_runtime_function_entry_panic_block(),
                        &[],
                        "",
                    );
                    self.builder.build_unreachable();
                }
            };
        }
    }

    pub fn emit_all(&mut self, mir: &'a MiddleIR) {
        self.function_value_ctx.entry_scope();
        insert_library_function(
            &mut self.function_value_ctx,
            self.memory_layout_ctx.get_mut_mir_type_context(),
            self.module.as_ref(),
        );
        for func in mir.module.iter() {
            self.emit_fn_declaration(func);
        }
        for func in mir.module.iter() {
            self.emit_fn(func);
        }
        self.function_value_ctx.exit_scope();
        self.module.verify().unwrap_or_else(|msg| {
            eprintln!("{}", msg.to_string());
            panic!("verification failed")
        });
    }
}

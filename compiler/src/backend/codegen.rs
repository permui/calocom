use std::{cell::RefCell, collections::HashMap, hash::Hash, rc::Rc};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::{self, Context},
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
    AddressSpace,
};

use super::memory::MemoryLayoutContext;
use crate::{
    midend::middle_ir::FuncDef,
    midend::{
        middle_ir::{self, BinOp, Block, Literal, MiddleIR, Value, VarDef, TypedValue},
        name_decoration::decorate_polymorphic_function,
        type_context::{SingletonType, Type},
    },
};

pub struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    memory_layout_ctx: MemoryLayoutContext<'ctx>,
    fn_map: HashMap<String, FunctionValue<'ctx>>,
    fn_name_map: HashMap<String, String>,
    var_map: HashMap<Rc<VarDef>, PointerValue<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
    pub fn new(name: &'ctx str, llvm_ctx: &'ctx Context, mir: &MiddleIR) -> Self {
        let module = llvm_ctx.create_module(name);
        let builder = llvm_ctx.create_builder();
        let ty_ctx = mir.ty_ctx.clone();
        CodeGen {
            context: llvm_ctx,
            module,
            builder,
            memory_layout_ctx: MemoryLayoutContext::new(ty_ctx, llvm_ctx),
            fn_map: HashMap::new(),
            fn_name_map: HashMap::new(),
            var_map: HashMap::new(),
        }
    }

    // set the insert position to the last non-terminator instruction
    fn set_insert_position(builder: &Builder, block: BasicBlock<'ctx>) {
        if let Some(terminator) = block.get_terminator() {
            builder.position_before(&terminator);
        } else {
            builder.position_at_end(block);
        }
    }

    // create stack allocation
    fn emit_local_alloca(
        memory_layout_ctx: &MemoryLayoutContext<'ctx>,
        builder: &Builder<'ctx>,
        block: BasicBlock<'ctx>,
        variables: &Vec<Rc<VarDef>>,
        var_map: &mut HashMap<Rc<VarDef>, PointerValue<'ctx>>,
        need_extra_ptr: bool,
    ) {
        CodeGen::set_insert_position(builder, block);
        for var in variables {
            let typ = memory_layout_ctx.get_llvm_type_by_idx(var.typ);
            let stack_slot = builder.build_alloca(
                if need_extra_ptr {
                    typ.ptr_type(AddressSpace::Generic).into()
                } else {
                    typ
                },
                var.name.as_str(),
            );
            var_map.insert(Rc::clone(var), stack_slot);
        }
    }

    // create all basic blocks but not fill the instructions
    fn emit_basic_blocks(
        ctx: &'ctx Context,
        func: FunctionValue<'ctx>,
        blocks: &Vec<Rc<RefCell<Block>>>,
    ) -> HashMap<String, BasicBlock<'ctx>> {
        let mut map = HashMap::new();
        let mut bbs = vec![];
        for block in blocks {
            let name = block.as_ref().borrow().name.clone();
            let bb = ctx.append_basic_block(func, name.as_str());
            map.insert(name, bb);
            bbs.push(bb);
        }
        map
    }

    fn emit_calocom_literal(
        ctx: &'ctx Context,
        builder: &Builder<'ctx>,
        module: &Module<'ctx>,
        value: &TypedValue,
        var_map: &HashMap<Rc<VarDef>, PointerValue<'ctx>>,
    ) {
    }

    fn emit_calocom_intrinsic_function(
        ctx: &'ctx Context,
        builder: &Builder<'ctx>,
        module: &Module<'ctx>,
        value: &TypedValue,
        var_map: &HashMap<Rc<VarDef>, PointerValue<'ctx>>,
    ) -> (bool, BasicValueEnum<'ctx>) {
        todo!()
    }


    // create a unboxed llvm value
    // NOTICE: now only calocom.i32 can be unboxed
    fn emit_unboxed_value(
        ctx: &'ctx Context,
        builder: &Builder<'ctx>,
        module: &Module<'ctx>,
        value: &TypedValue,
        var_map: &HashMap<Rc<VarDef>, PointerValue<'ctx>>,
    ) -> BasicValueEnum<'ctx> {
        let TypedValue { typ, val } = value;
        let value = val;
        match value {
            Value::Call(_, _) => {
                let bv = CodeGen::emit_calocom_value(ctx, builder, module, value, var_map);
                // unable to check the type here
                let bv = builder.build_load(bv.into_pointer_value(), "");
                bv
            }
            Value::Op(op, l, r) => {
                let lhs = CodeGen::emit_unboxed_value(ctx, builder, module, l, var_map);
                let rhs = CodeGen::emit_unboxed_value(ctx, builder, module, r, var_map);

                let res = if lhs.is_int_value() && rhs.is_int_value() {
                    match op {
                        BinOp::Plus => builder
                            .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Sub => builder
                            .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Mult => builder
                            .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Div => builder
                            .build_int_signed_div(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Mod => builder
                            .build_int_signed_rem(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                    }
                } else {
                    panic!("could not take such operation: {:?}", value)
                };
                res
            }
            Value::Imm(lit) => match lit {
                Literal::Int(i) => ctx
                    .i32_type()
                    .const_int(*i as u64, false)
                    .as_basic_value_enum(),
                Literal::Str(s) => panic!("unable to create unboxed string literal"),
                Literal::Bool(b) => ctx
                    .i32_type()
                    .const_int(*b as u64, false)
                    .as_basic_value_enum(),
            },
            Value::Unit => panic!("unable to create unboxed unit value"),
            Value::Intrinsic(name, params) => {
                todo!()
            }
            Value::VarRef(var) => {
                let mut bv = CodeGen::emit_calocom_value(ctx, builder, module, value, var_map);
                if matches!(var.typ, SingletonType::I32) {
                    bv = builder.build_load(bv.into_pointer_value(), "");
                }
                bv
            }
        }
    }

    fn emit_calocom_value(
        ctx: &'ctx Context,
        builder: &Builder<'ctx>,
        module: &Module<'ctx>,
        value: &Value,
        var_map: &HashMap<Rc<VarDef>, PointerValue<'ctx>>,
    ) -> BasicValueEnum<'ctx> {
        match value {
            Value::Call(_, _) => todo!(),
            Value::Op(_, _, _) => {
                todo!()
            }
            Value::Imm(_) => todo!(),
            Value::Unit => todo!(),
            Value::Intrinsic(_, _) => todo!(),
            Value::VarRef(var) => {
                let ptr = var_map.get(var).unwrap();
                let bv: BasicValueEnum = builder.build_load(*ptr, "");
                bv
            }
        }
    }

    fn emit_stmt(
        ctx: &'ctx Context,
        builder: &Builder,
        module: &Module,
        blocks: &Block,
        llvm_block: &BasicBlock,
    ) {
        for stmt in &blocks.stmts {}
    }

    fn emit_basic_block_terminators(
        context: &'ctx Context,
        builder: &Builder,
        ret_var_ptr: PointerValue<'ctx>,
        blocks: &[Rc<RefCell<Block>>],
        block_map: &HashMap<String, BasicBlock>,
        var_map: &HashMap<Rc<VarDef>, PointerValue<'ctx>>,
    ) {
        for block in blocks.iter() {
            let llvm_block = block_map
                .get(block.as_ref().borrow().name.as_str())
                .unwrap();
            builder.position_at_end(*llvm_block);
            match &block.as_ref().borrow().terminator {
                middle_ir::Terminator::Select(var, choices, other) => {
                    let stack_slot = var_map.get(var).unwrap();
                    let loaded_value = builder.build_load(*stack_slot, "");
                    let other = block_map
                        .get(other.as_ref().borrow().name.as_str())
                        .unwrap();
                    let choices: Vec<(_, _)> = choices
                        .iter()
                        .map(|(lit, block)| {
                            if let middle_ir::Literal::Int(i) = lit.as_ref() {
                                let block = block_map
                                    .get(block.as_ref().borrow().name.as_str())
                                    .unwrap();
                                let llvm_const_int = context.i32_type().const_int(*i as u64, false);
                                (llvm_const_int, *block)
                            } else {
                                panic!(
                                    "internal error: middle ir select choice has wrong value type"
                                )
                            }
                        })
                        .collect();
                    builder.build_switch(loaded_value.into_int_value(), *other, &choices[..])
                }
                middle_ir::Terminator::Jump(x) => {
                    let target = block_map.get(x.as_ref().borrow().name.as_str()).unwrap();
                    builder.build_unconditional_branch(*target)
                }
                middle_ir::Terminator::Return => {
                    let ret_var = builder.build_load(ret_var_ptr, "ret.var");
                    builder.build_return(Some(&ret_var))
                }
                middle_ir::Terminator::Panic => builder.build_unreachable(),
            };
        }
    }

    fn emit_function_definition(&mut self, fn_def: &FuncDef) {
        let FuncDef {
            name,
            param_def,
            var_def,
            tmp_def,
            mem_ref,
            ret_def,
            blocks,
            unwrapped_def,
        } = fn_def;

        let ret_type_idx = ret_def.as_ref().unwrap().typ;
        let ret_type = self
            .memory_layout_ctx
            .get_llvm_type_by_idx(ret_type_idx)
            .ptr_type(AddressSpace::Generic);
        let mut param_type: Vec<BasicMetadataTypeEnum<'ctx>> = vec![];

        for var in param_def.iter() {
            let typ = self
                .memory_layout_ctx
                .get_llvm_type_by_idx(var.1.typ)
                .ptr_type(AddressSpace::Generic);
            param_type.push(typ.into());
        }

        let fn_type = MemoryLayoutContext::get_fn_type_of_basic_type_enum(
            ret_type.into(),
            &param_type[..],
            false,
        );
        let decorated_name = decorate_polymorphic_function(
            &[name.clone()],
            &[],
            &self.memory_layout_ctx.get_mir_type_idx(ret_type_idx),
            &param_def
                .iter()
                .map(|param| self.memory_layout_ctx.get_mir_type_idx(param.1.typ))
                .collect::<Vec<Type>>()[..],
        );

        self.fn_name_map
            .insert(name.clone(), decorated_name.clone());
        let func = self
            .module
            .add_function(decorated_name.as_str(), fn_type, None);

        self.fn_map.insert(decorated_name, func);
        let block_map = CodeGen::emit_basic_blocks(self.context, func, blocks);

        let entry_block = *block_map.get("entry").unwrap();
        self.builder.position_at_end(entry_block);

        let typ = self
            .memory_layout_ctx
            .get_llvm_type_by_idx(ret_def.as_ref().unwrap().typ)
            .ptr_type(AddressSpace::Generic);
        let ret_var_ptr = self.builder.build_alloca(typ, "ret.var.ptr");

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            entry_block,
            var_def,
            &mut self.var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            entry_block,
            tmp_def,
            &mut self.var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            entry_block,
            unwrapped_def,
            &mut self.var_map,
            false,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            entry_block,
            mem_ref,
            &mut self.var_map,
            true,
        );

        CodeGen::emit_basic_block_terminators(
            self.context,
            &self.builder,
            ret_var_ptr,
            blocks,
            &block_map,
            &self.var_map,
        );
    }

    pub fn emit_all(&mut self, mir: &MiddleIR) {
        for func in mir.module.iter() {
            self.emit_function_definition(func);
        }
        self.module.verify().unwrap();
        self.module.write_bitcode_to_file(
            &std::fs::File::options()
                .write(true)
                .create(true)
                .open("../bitcode.bc")
                .unwrap(),
            true,
            false,
        );
    }
}

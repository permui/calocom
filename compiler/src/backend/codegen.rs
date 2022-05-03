use std::{cell::RefCell, collections::HashMap, path::Path, rc::Rc};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType},
    values::{AnyValue, BasicValue, BasicValueEnum, FunctionValue, PointerValue},
    AddressSpace,
};

use super::{memory::MemoryLayoutContext, runtime::CoreLibrary};
use crate::{
    midend::middle_ir::FuncDef,
    midend::{
        middle_ir::{self, BinOp, Block, Literal, MiddleIR, TypedValue, Value, VarDef},
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
        let mut module = llvm_ctx.create_module(name);
        let builder = llvm_ctx.create_builder();
        let ty_ctx = mir.ty_ctx.clone();
        module.link_calocom_runtime_module(Path::new("../calocom_runtime.ll"));
        let mut calocom_types = vec![];
        for idx in SingletonType::OBJECT..=SingletonType::C_I32 {
            calocom_types.push(module.get_calocom_type(idx.into()));
        }
        let mem_layout_ctx = MemoryLayoutContext::new(ty_ctx, llvm_ctx, calocom_types.as_slice());
        CodeGen {
            context: llvm_ctx,
            module,
            builder,
            memory_layout_ctx: mem_layout_ctx,
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

    fn emit_calocom_intrinsic_function(
        &self,
        need_boxing: bool,
        value: &TypedValue,
    ) -> BasicValueEnum<'ctx> {
        todo!()
    }

    // create a unboxed llvm value
    // NOTICE: now only calocom.i32 can be unboxed
    fn emit_unboxed_value(&self, typed_value: &TypedValue) -> BasicValueEnum<'ctx> {
        let TypedValue { typ, val } = typed_value;
        match val {
            Value::Call(_, _) => {
                let mut bv = self.emit_calocom_value(typed_value);

                if matches!(*typ, SingletonType::I32) {
                    bv = self.builder.build_load(bv.into_pointer_value(), "");
                }

                bv
            }
            Value::Op(op, l, r) => {
                let lhs = self.emit_unboxed_value(l);
                let rhs = self.emit_unboxed_value(r);

                let res = if matches!(l.typ, SingletonType::I32 | SingletonType::C_I32)
                    || matches!(r.typ, SingletonType::I32 | SingletonType::C_I32)
                {
                    match op {
                        BinOp::Plus => self
                            .builder
                            .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Sub => self
                            .builder
                            .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Mult => self
                            .builder
                            .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Div => self
                            .builder
                            .build_int_signed_div(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                        BinOp::Mod => self
                            .builder
                            .build_int_signed_rem(lhs.into_int_value(), rhs.into_int_value(), "")
                            .as_basic_value_enum(),
                    }
                } else {
                    panic!("could not take such operation: {:?}", typed_value)
                };

                res
            }
            Value::Imm(lit) => self.emit_literal_value(false, lit),
            Value::Unit => panic!("unable to create unboxed unit value"),
            Value::Intrinsic(_, _) => self.emit_calocom_intrinsic_function(false, typed_value),
            Value::VarRef(var) => {
                let mut bv = self.emit_calocom_value(typed_value);
                // only promote i32 value
                if matches!(var.typ, SingletonType::I32) {
                    bv = self.builder.build_load(bv.into_pointer_value(), "");
                }
                bv
            }
        }
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
                            self.module.get_runtime_function_alloc_i32_literal(),
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
                let b = self
                    .context
                    .i32_type()
                    .const_int(*b as u64, false)
                    .as_basic_value_enum();
                if need_boxing {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_alloc_bool_literal(),
                            &[b.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    b
                }
            }
        }
    }

    fn emit_calocom_value(&self, typed_value: &TypedValue) -> BasicValueEnum<'ctx> {
        let TypedValue { typ, val } = typed_value;
        match val {
            Value::Call(path, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.emit_calocom_value(arg).into())
                    .collect();
                let decorated_name = self.fn_name_map.get(path.items[0].as_str()).unwrap();
                let function = self.fn_map.get(decorated_name).unwrap();
                // NOTE: void function not allowed in calocom
                self.builder
                    .build_call(*function, &args[..], "")
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            Value::Op(op, _, _) => {
                let v = self.emit_unboxed_value(typed_value);
                if *typ == SingletonType::I32 {
                    self.builder
                        .build_call(
                            self.module.get_runtime_function_alloc_i32_literal(),
                            &[v.into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                } else {
                    unimplemented!()
                }
            }
            Value::Imm(lit) => self.emit_literal_value(true, lit),
            Value::Unit => self
                .builder
                .build_call(self.module.get_runtime_function_alloc_unit(), &[], "")
                .try_as_basic_value()
                .left()
                .unwrap(),
            Value::Intrinsic(_, _) => self.emit_calocom_intrinsic_function(true, typed_value),
            Value::VarRef(var) => {
                let ptr = self.var_map.get(var).unwrap();
                let bv: BasicValueEnum = self.builder.build_load(*ptr, "");
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
        &self,
        ret_var_ptr: PointerValue<'ctx>,
        blocks: &[Rc<RefCell<Block>>],
        block_map: &HashMap<String, BasicBlock>,
    ) {
        for block in blocks.iter() {
            let llvm_block = block_map
                .get(block.as_ref().borrow().name.as_str())
                .unwrap();
            self.builder.position_at_end(*llvm_block);
            match &block.as_ref().borrow().terminator {
                middle_ir::Terminator::Select(var, choices, other) => {
                    let stack_slot = self.var_map.get(var).unwrap();
                    let loaded_value = self.builder.build_load(*stack_slot, "");
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
                                let llvm_const_int =
                                    self.context.i32_type().const_int(*i as u64, false);
                                (llvm_const_int, *block)
                            } else {
                                panic!(
                                    "internal error: middle ir select choice has wrong value type"
                                )
                            }
                        })
                        .collect();
                    self.builder
                        .build_switch(loaded_value.into_int_value(), *other, &choices[..]);
                }
                middle_ir::Terminator::Jump(x) => {
                    let target = block_map.get(x.as_ref().borrow().name.as_str()).unwrap();
                    self.builder.build_unconditional_branch(*target);
                }
                middle_ir::Terminator::Return => {
                    let ret_var = self.builder.build_load(ret_var_ptr, "ret.var");
                    self.builder.build_return(Some(&ret_var));
                }
                middle_ir::Terminator::Panic => {
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

        self.emit_basic_block_terminators(ret_var_ptr, blocks, &block_map);
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

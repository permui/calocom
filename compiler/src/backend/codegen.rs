use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    path::Path,
    rc::Rc,
};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, PointerType},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
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
    pub module: Module<'ctx>,
    builder: Builder<'ctx>,
    memory_layout_ctx: MemoryLayoutContext<'ctx>,
    fn_map: HashMap<String, FunctionValue<'ctx>>,
    ext_fn_map: HashMap<Vec<String>, FunctionValue<'ctx>>,
    fn_name_map: HashMap<String, String>,
    var_map: HashMap<Rc<VarDef>, PointerValue<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
    pub fn new(name: &'ctx str, llvm_ctx: &'ctx Context, mir: &MiddleIR, path: &Path) -> Self {
        let mut module = llvm_ctx.create_module(name);
        let builder = llvm_ctx.create_builder();
        let ty_ctx = mir.ty_ctx.clone();
        module.link_calocom_runtime_module(path);
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
            ext_fn_map: HashMap::new(),
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

    // create stack allocation
    fn emit_local_alloca(
        memory_layout_ctx: &MemoryLayoutContext<'ctx>,
        builder: &Builder<'ctx>,
        block: BasicBlock<'ctx>,
        variables: &Vec<Rc<VarDef>>,
        var_map: &mut HashMap<Rc<VarDef>, PointerValue<'ctx>>,
        need_extra_ptr: bool,
    ) {
        CodeGen::set_insert_position_before_terminator(builder, &block);
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

        let alloca_bb = ctx.append_basic_block(func, "alloca");
        map.insert("alloca".to_string(), alloca_bb);
        bbs.push(alloca_bb);

        for block in blocks {
            let name = block.as_ref().borrow().name.clone();
            let bb = ctx.append_basic_block(func, name.as_str());
            map.insert(name, bb);
            bbs.push(bb);
        }
        map
    }

    // NOTICE: 2022.4 clang & llvm begin to fully support opaque pointer type,
    // llvm may deprecate normal typed pointer in the future
    fn emit_pointer_cast(
        &self,
        ptr: PointerValue<'ctx>,
        typ: PointerType<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        self.builder
            .build_pointer_cast(ptr, typ, "")
            .as_basic_value_enum()
    }

    fn emit_calocom_intrinsic_function(
        &self,
        _need_boxing: bool,
        typed_value: &TypedValue,
    ) -> BasicValueEnum<'ctx> {
        let TypedValue { typ, val } = typed_value;
        match val {
            Value::Intrinsic(name, args) => {
                match *name {
                    "calocom.extract_tag" => {
                        assert!(args.len() == 1);

                        let obj = self.emit_calocom_value(&args[0]);
                        let enum_type = self
                            .module
                            .get_runtime_type__Enum()
                            .ptr_type(AddressSpace::Generic);
                        let obj = self.emit_pointer_cast(obj.into_pointer_value(), enum_type);

                        self.builder
                            .build_call(
                                self.module.get_runtime_function_extract_enum_tag(),
                                &[obj.into()],
                                name,
                            )
                            .try_as_basic_value()
                            .left()
                            .unwrap()
                            .as_basic_value_enum()
                    }
                    "calocom.extract_field" => {
                        let enum_type = self
                            .module
                            .get_runtime_type__Enum()
                            .ptr_type(AddressSpace::Generic);
                        let obj = self.emit_calocom_value(&args[0]);
                        let obj = self.emit_pointer_cast(obj.into_pointer_value(), enum_type);

                        let ctor_idx = match args[1].val {
                            Value::Imm(Literal::Int(i)) => i,
                            _ => panic!("internal error: expect a literal here"),
                        };

                        let field_idx = match args[2].val {
                            Value::Imm(Literal::Int(i)) => i,
                            _ => panic!("internal error: expect a literal here"),
                        };

                        let ctor_idx = self.context.i32_type().const_int(ctor_idx as u64, false);
                        let field_idx = self.context.i32_type().const_int(field_idx as u64, false);

                        let result = self
                            .builder
                            .build_call(
                                self.module.get_runtime_function_extract_enum_field(),
                                &[obj.into(), ctor_idx.into(), field_idx.into()],
                                name,
                            )
                            .try_as_basic_value()
                            .left()
                            .unwrap()
                            .as_basic_value_enum();

                        self.emit_pointer_cast(
                            result.into_pointer_value(),
                            self.memory_layout_ctx
                                .get_llvm_type_by_idx(*typ)
                                .ptr_type(AddressSpace::Generic),
                        )
                    }
                    "calocom.construct" => {
                        let ctor_idx = match args[0].val {
                            Value::Imm(Literal::Int(i)) => i,
                            _ => panic!("internal error: expect a literal here"),
                        };
                        let ctor_idx = self.context.i32_type().const_int(ctor_idx as u64, false);
                        let obj_typ = self
                            .module
                            .get_runtime_type__Object()
                            .ptr_type(AddressSpace::Generic);
                        let obj = self.emit_calocom_value(&args[0]);
                        let obj = self.emit_pointer_cast(obj.into_pointer_value(), obj_typ);

                        let result = self
                            .builder
                            .build_call(
                                self.module.get_runtime_function_construct_enum(),
                                &[ctor_idx.into(), obj.into()],
                                name,
                            )
                            .try_as_basic_value()
                            .left()
                            .unwrap()
                            .as_basic_value_enum();

                        self.emit_pointer_cast(
                            result.into_pointer_value(),
                            self.memory_layout_ctx
                                .get_llvm_type_by_idx(*typ)
                                .ptr_type(AddressSpace::Generic),
                        )
                    }
                    "calocom.get_address" => {
                        let lhs = match &args[0].val {
                            Value::VarRef(val) => val,
                            _ => panic!(
                                "internal error: get_address can only be applied to a VarRef"
                            ),
                        };
                        let rhs = match &args[1].val {
                            Value::VarRef(val) => val,
                            _ => panic!(
                                "internal error: get_address can only be applied to a VarRef"
                            ),
                        };
                        let left_ptr = self.var_map.get(lhs).unwrap();
                        let right_ptr = self.var_map.get(rhs).unwrap();
                        self.builder
                            .build_store(*left_ptr, right_ptr.as_basic_value_enum());

                        // dummy: don't use the value
                        self.context.i32_type().const_zero().as_basic_value_enum()
                    }
                    "calocom.dereference" => {
                        let ptr = self.emit_calocom_value(&args[0]).into_pointer_value();
                        self.builder.build_load(ptr, "").as_basic_value_enum()
                    }
                    "calocom.store" => {
                        let ptr = self.emit_calocom_value(&args[0]).into_pointer_value();
                        let rhs = self.emit_calocom_value(&args[1]);
                        self.builder.build_store(ptr, rhs);

                        // dummy: don't use the value
                        self.context.i32_type().const_zero().as_basic_value_enum()
                    }
                    "calocom.erase_type" => {
                        let obj_typ = self
                            .module
                            .get_runtime_type__Object()
                            .ptr_type(AddressSpace::Generic);
                        let ptr = self.emit_calocom_value(&args[0]).into_pointer_value();

                        self.emit_pointer_cast(ptr, obj_typ).as_basic_value_enum()
                    }
                    _ => unimplemented!("unimplemented intrinsic {}", name),
                }
            }
            _ => panic!("internal error"),
        }
    }

    // create a unboxed llvm value
    // NOTICE: now only calocom.i32 can be unboxed
    fn emit_unboxed_value(&self, typed_value: &TypedValue) -> BasicValueEnum<'ctx> {
        let TypedValue { typ, val } = typed_value;
        match val {
            Value::ExtCall(_, _) | Value::Call(_, _) | Value::VarRef(_) => {
                let mut bv = self.emit_calocom_value(typed_value);
                // only promote i32 value
                if matches!(*typ, SingletonType::I32) {
                    bv = self
                        .builder
                        .build_call(
                            self.module.get_runtime_function_extract_i32(),
                            &[bv.into(), self.context.i32_type().const_zero().into()],
                            "",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap();
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
            Value::ExtCall(path, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.emit_calocom_value(arg).into())
                    .collect();
                let function = self
                    .ext_fn_map
                    .get(&path.items)
                    .unwrap_or_else(|| panic!("can't found called function {}", path));
                // NOTE: void function not allowed in calocom
                self.builder
                    .build_call(*function, &args[..], "")
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
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
            Value::Op(_, _, _) => {
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
                let ptr = self
                    .var_map
                    .get(var)
                    .unwrap_or_else(|| panic!("variable map doesn't contains {}", var.name));
                let bv: BasicValueEnum = self.builder.build_load(*ptr, "");
                bv
            }
        }
    }

    fn emit_stmts(&self, block: &Ref<Block>, llvm_block: &BasicBlock) {
        CodeGen::set_insert_position_before_terminator(&self.builder, llvm_block);
        for stmt in &block.stmts {
            let rhs = self.emit_calocom_value(stmt.right.as_ref().unwrap());
            if let Some(left) = &stmt.left {
                let &ptr = self
                    .var_map
                    .get(left)
                    .unwrap_or_else(|| panic!("variable map doesn't contains {}", left.name));
                self.builder.build_store(ptr, rhs);
            }
        }
    }

    fn emit_all_stmts(
        &self,
        blocks: &Vec<Rc<RefCell<Block>>>,
        block_map: &HashMap<String, BasicBlock>,
    ) {
        for bb in blocks {
            let bb = bb.borrow();
            let name = &bb.name;
            let llvm_bb = block_map.get(name.as_str()).unwrap();
            self.emit_stmts(&bb, llvm_bb);
        }
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
                    let stack_slot = self
                        .var_map
                        .get(var)
                        .unwrap_or_else(|| panic!("variable map doesn't contains {}", var.name));
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

    fn emit_arguments_store(&self, func: FunctionValue, param_def: &[Rc<VarDef>]) {
        for (idx, var) in param_def.iter().enumerate() {
            let stack_slot = self
                .var_map
                .get(&Rc::clone(var))
                .expect("expect a slack slot");
            let arg = func.get_nth_param(idx as u32).expect("expect an argument");
            self.builder.build_store(*stack_slot, arg);
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
                .get_llvm_type_by_idx(var.typ)
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
                .map(|param| self.memory_layout_ctx.get_mir_type_idx(param.typ))
                .collect::<Vec<Type>>()[..],
        );

        self.fn_name_map
            .insert(name.clone(), decorated_name.clone());

        let func = self
            .module
            .get_function(decorated_name.as_str())
            .unwrap_or_else(|| {
                self.module
                    .add_function(decorated_name.as_str(), fn_type, None)
            });

        self.fn_map.insert(decorated_name, func);
        let block_map = CodeGen::emit_basic_blocks(self.context, func, blocks);

        let alloca_block = *block_map.get("alloca").unwrap();
        self.builder.position_at_end(alloca_block);

        let typ = self
            .memory_layout_ctx
            .get_llvm_type_by_idx(ret_def.as_ref().unwrap().typ)
            .ptr_type(AddressSpace::Generic);
        let ret_var_ptr = self.builder.build_alloca(typ, "ret.var.ptr");

        self.var_map
            .insert(Rc::clone(ret_def.as_ref().unwrap()), ret_var_ptr);

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            param_def,
            &mut self.var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            var_def,
            &mut self.var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            tmp_def,
            &mut self.var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            unwrapped_def,
            &mut self.var_map,
            false,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            mem_ref,
            &mut self.var_map,
            true,
        );
        self.emit_arguments_store(func, param_def);
        self.builder
            .build_unconditional_branch(*block_map.get("entry").unwrap());

        self.emit_all_stmts(blocks, &block_map);
        self.emit_basic_block_terminators(ret_var_ptr, blocks, &block_map);
    }

    pub fn insert_external_function(&mut self) {
        for (path, typ) in self
            .memory_layout_ctx
            .get_mir_type_context()
            .ext_poly_ftypes
            .iter()
        {
            let decorated_name = decorate_polymorphic_function(
                path.as_slice(),
                &[],
                &self.memory_layout_ctx.get_mir_type_idx(typ.0),
                &typ.1
                    .iter()
                    .map(|typ| self.memory_layout_ctx.get_mir_type_idx(*typ))
                    .collect::<Vec<Type>>()[..],
            );

            let ext_fn = self
                .module
                .get_function(decorated_name.as_str())
                .unwrap_or_else(|| panic!("can't found function {:?} : {}", path, decorated_name));

            self.ext_fn_map.insert(path.clone(), ext_fn);
        }
    }

    pub fn emit_all(&mut self, mir: &MiddleIR) {
        self.insert_external_function();
        for func in mir.module.iter() {
            self.emit_function_definition(func);
        }
        self.module.verify().unwrap();
    }
}

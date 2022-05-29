use std::{
    collections::HashMap,
    path::{self, Path},
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

use slotmap::SlotMap;

use super::{memory::MemoryLayoutContext, name_mangling::Mangling, runtime::CoreLibrary};
use crate::{
    ast::Literal,
    common::name_context::NameContext,
    midend::middle_ir::{
        Block, BlockRef, FuncDef, Operand, OperandEnum, Terminator, Value, VarDef, VarDefRef,
    },
    MiddleIR,
};

#[derive(Debug)]
pub struct FunctionEmissionState<'ctx> {
    var_map: HashMap<VarDefRef, PointerValue<'ctx>>,
    block_map: HashMap<BlockRef, BasicBlock<'ctx>>,
    func: FunctionValue<'ctx>,
    alloca_block: BasicBlock<'ctx>,
    ret_value: PointerValue<'ctx>,
}

pub struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Rc<Module<'ctx>>,
    memory_layout_ctx: MemoryLayoutContext<'ctx>,
    function_value_ctx: NameContext<FunctionValue<'ctx>>,
    builder: Builder<'ctx>,
    current_function: Option<FunctionEmissionState<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
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
        need_extra_ptr: bool,
    ) {
        CodeGen::set_insert_position_before_terminator(
            &self.builder,
            &self.current_function.as_ref().unwrap().alloca_block,
        );
        for (var_ref, var) in slots {
            let typ = self.memory_layout_ctx.get_llvm_type(var.typ);
            let stack_slot = self.builder.build_alloca(
                if need_extra_ptr {
                    typ.ptr_type(AddressSpace::Generic).into()
                } else {
                    typ
                },
                var.name.as_str(),
            );
            self.current_function
                .as_mut()
                .unwrap()
                .var_map
                .insert(var_ref, stack_slot);
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

    fn emit_fn(&mut self, mir_func: &FuncDef) {
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
            entry_block,
            return_block,
            panic_block,
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

        // create all basic blocks and alloca block
        let (block_map, entry_block) = CodeGen::emit_basic_blocks(self.context, func, blocks);
        let alloca_block = self.context.append_basic_block(func, "alloca");
        CodeGen::set_insert_position_before_terminator(&self.builder, &alloca_block);

        // build the alloca of return value and insert it to map
        let mut var_map = HashMap::new();
        let ret_ptr = self
            .builder
            .build_alloca(ret_llvm_type.ptr_type(AddressSpace::Generic), "ret.var.ptr");
        var_map.insert(ret_var_ref, ret_ptr);

        self.current_function = Some(FunctionEmissionState {
            var_map,
            block_map,
            func,
            alloca_block,
            ret_value: ret_ptr,
        });

        self.emit_local_alloca(variables, params, true);
        self.emit_local_alloca(variables, locals, true);
        self.emit_local_alloca(variables, temporaries, true);
        self.emit_local_alloca(variables, obj_reference, true);
        self.emit_local_alloca(variables, unwrapped, false);

        // store the arguments into local variables
        self.emit_arguments_store(params);
        // extract the captured variables from closure parameter
        self.emit_captured_store(captured);
        self.builder
            .build_unconditional_branch(entry_block.unwrap());

        self.emit_all_stmts(blocks);
        self.emit_basic_block_terminators(ret_ptr, blocks);
    }

    fn emit_all_stmts(&self, blocks: &SlotMap<BlockRef, Block>) {
        let block_map = &self.current_function.as_ref().unwrap().block_map;
        for (bb_ref, bb) in blocks {
            let llvm_bb = block_map.get(&bb_ref).unwrap();
            self.emit_stmts(bb, llvm_bb);
        }
    }

    fn emit_stmts(&self, block: &Block, llvm_block: &BasicBlock) {
        CodeGen::set_insert_position_before_terminator(&self.builder, llvm_block);

        let var_map = &self.current_function.as_ref().unwrap().var_map;
        for stmt in &block.stmts {
            let rhs = self.emit_calocom_value(stmt.right.as_ref().unwrap());
            if let Some(left) = &stmt.left {
                let &ptr = var_map
                    .get(left)
                    .unwrap_or_else(|| panic!("variable map doesn't contains the var"));
                self.builder.build_store(ptr, rhs);
            }
        }
    }

    fn emit_operand(&self, operand: &Operand) -> BasicValueEnum<'ctx> {
        let Operand { val, .. } = operand;
        match val.as_ref() {
            OperandEnum::Imm(i) => self
                .context
                .i32_type()
                .const_int(*i as u64, false)
                .as_basic_value_enum(),
            OperandEnum::Literal(lit) => self.emit_literal_value(true, lit),
            OperandEnum::Var(var) => {
                let ptr = self
                    .current_function
                    .as_ref()
                    .unwrap()
                    .var_map
                    .get(var)
                    .unwrap_or_else(|| panic!("variable map doesn't contains the var"));
                let bv: BasicValueEnum = self.builder.build_load(*ptr, "");
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
                    unreachable!()
                }
            }
        }
    }

    fn emit_calocom_value(&self, value: &Value) -> BasicValueEnum<'ctx> {
        let Value { typ, val } = value;
        use crate::midend::middle_ir::ValueEnum::*;
        match val {
            Call(path, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.emit_operand(arg).into())
                    .collect();
                let function = self.function_value_ctx.find_symbol(path).unwrap();
                // NOTE: void function not allowed in calocom, so choose the left
                self.builder
                    .build_call(function, &args[..], "")
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            ExtCall(path, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.emit_operand(arg).into())
                    .collect();
                let function = self.function_value_ctx.find_symbol(path).unwrap();
                // NOTE: void function not allowed in calocom, so choose the left
                self.builder
                    .build_call(function, &args[..], "")
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            ExtractClosureCapture(_, _) => todo!(),
            ClosureCall(_, _) => todo!(),
            MakeClosure { .. } => todo!(),
            BinaryOp(_, _, _) => todo!(),
            UnaryOp(_, _) => todo!(),
            MakeTuple(_) => todo!(),
            Construct(_, _) => todo!(),
            Intrinsic(_, _) => todo!(),
            Index(_, _) => todo!(),
            Operand(_) => todo!(),
            ExtractTupleField(_, _) => todo!(),
            ExtractEnumField(_, _, _) => todo!(),
            ExtractEnumTag(obj) => {
                let obj = self.emit_operand(obj);
                let enum_type = self
                    .module
                    .get_runtime_type__Enum()
                    .ptr_type(AddressSpace::Generic);
                let obj = self.emit_pointer_cast(obj.into_pointer_value(), enum_type);

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
            CombineByFoldWithAnd1(_) => todo!(),
            UnboxBool(_) => todo!(),
            UnboxInt32(_) => todo!(),
            CompareStr(_, _) => todo!(),
            CompareCInt32(_, _) => todo!(),
        }
    }

    fn emit_arguments_store(&mut self, params: &[VarDefRef]) {
        let func = self.current_function.as_ref().unwrap().func;
        let var_map = &mut self.current_function.as_mut().unwrap().var_map;
        for (idx, var) in params.iter().enumerate() {
            let stack_slot = var_map.get(var).expect("expect a slack slot");
            let arg = func.get_nth_param(idx as u32).expect("expect an argument");
            self.builder.build_store(*stack_slot, arg);
        }
    }

    fn emit_captured_store(&self, captured: &[VarDefRef]) {
        todo!()
    }

    fn emit_basic_block_terminators(
        &self,
        ret_var_ptr: PointerValue<'ctx>,
        blocks: &SlotMap<BlockRef, Block>,
    ) {
        let state = self.current_function.as_ref().unwrap();
        let ret_var_ptr = state.ret_value;
        let var_map = &state.var_map;
        let block_map = &state.block_map;

        for (block_ref, block) in blocks.iter() {
            let llvm_block = block_map.get(&block_ref).unwrap();
            self.builder.position_at_end(*llvm_block);

            match &block.terminator {
                Terminator::Branch(var, then, or) => todo!(),
                Terminator::Select(var, choices, other) => todo!(),
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

    pub fn emit_all(&mut self, mir: &MiddleIR) {
        for func in mir.module.iter() {
            self.emit_fn(func);
        }
        self.module.verify().unwrap();
    }
}

use std::{collections::HashMap, path::Path, rc::Rc};

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
    common::name_context::NameContext,
    midend::middle_ir::{Block, BlockRef, FuncDef, Terminator, Value, VarDef, VarDefRef},
    MiddleIR,
};

#[derive(Debug)]
pub struct FunctionEmissionState<'ctx> {
    variable_map: HashMap<VarDefRef, PointerValue<'ctx>>,
    block_map: HashMap<BlockRef, BasicBlock<'ctx>>,
    current_func: FunctionValue<'ctx>,
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
        memory_layout_ctx: &MemoryLayoutContext<'ctx>,
        builder: &Builder<'ctx>,
        block: BasicBlock<'ctx>,
        slots: &SlotMap<VarDefRef, VarDef>,
        variables: &[VarDefRef],
        variable_value_ctx: &mut HashMap<VarDefRef, PointerValue<'ctx>>,
        need_extra_ptr: bool,
    ) {
        CodeGen::set_insert_position_before_terminator(builder, &block);
        for (var_ref, var) in slots {
            let typ = memory_layout_ctx.get_llvm_type(var.typ);
            let stack_slot = builder.build_alloca(
                if need_extra_ptr {
                    typ.ptr_type(AddressSpace::Generic).into()
                } else {
                    typ
                },
                var.name.as_str(),
            );
            variable_value_ctx.insert(var_ref, stack_slot);
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

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            variables,
            params,
            &mut var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            variables,
            locals,
            &mut var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            variables,
            temporaries,
            &mut var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            variables,
            obj_reference,
            &mut var_map,
            true,
        );

        CodeGen::emit_local_alloca(
            &self.memory_layout_ctx,
            &self.builder,
            alloca_block,
            variables,
            unwrapped,
            &mut var_map,
            false,
        );

        self.emit_arguments_store(func, &var_map, params);
        self.builder
            .build_unconditional_branch(entry_block.unwrap());

        self.emit_basic_block_terminators(ret_ptr, blocks, &block_map, &var_map);
    }

    fn emit_arguments_store(
        &self,
        func: FunctionValue,
        var_map: &HashMap<VarDefRef, PointerValue<'ctx>>,
        param_def: &[VarDefRef],
    ) {
        for (idx, var) in param_def.iter().enumerate() {
            let stack_slot = var_map.get(var).expect("expect a slack slot");
            let arg = func.get_nth_param(idx as u32).expect("expect an argument");
            self.builder.build_store(*stack_slot, arg);
        }
    }

    fn emit_basic_block_terminators(
        &self,
        ret_var_ptr: PointerValue<'ctx>,
        blocks: &SlotMap<BlockRef, Block>,
        block_map: &HashMap<BlockRef, BasicBlock>,
        var_map: &HashMap<VarDefRef, PointerValue>,
    ) {
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

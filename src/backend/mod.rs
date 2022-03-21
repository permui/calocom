use crate::ast;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{AnyTypeEnum, BasicMetadataTypeEnum};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
enum Type {
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Enum(Vec<Type>),
    Unit,
}

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    sym_scope: Vec<HashSet<String>>,
    ty_env: HashMap<String, Type>,
    ty_pool: HashMap<Type, AnyTypeEnum<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
    fn new(name: &'ctx str, context: &'ctx Context) -> Self {
        let module = context.create_module(name);
        let builder = context.create_builder();
        CodeGen {
            context,
            module,
            builder,
            sym_scope: Default::default(),
            ty_env: Default::default(),
            ty_pool: Default::default(),
        }
    }

    fn entry_symbol_scope(&mut self) {
        self.sym_scope.push(Default::default());
    }

    fn exit_symbol_scope(&mut self) {
        self.sym_scope.pop();
    }

    fn push_symbol(&mut self, sym_name: &String) {
        let mut set = self.sym_scope.last_mut().unwrap();
        set.insert(sym_name.clone());
    }

    fn create_import(&mut self, ref_path: &ast::RefPath) {}

    fn create_data_type(&mut self, date_def: &ast::DataDef) {
        let ast::DataDef { name, con_list } = date_def;
        if self.ty_env.contains_key(name) {
            panic!("data type redefined")
        }
        todo!()
    }

    fn convert_ast_type_to_type(&self, typ: &ast::Type) -> Type {
        match typ {
            ast::Type::Arrow(_, _) => todo!(),
            ast::Type::Tuple(_) => todo!(),
            ast::Type::Enum(_) => todo!(),
            ast::Type::Unit => todo!(),
            ast::Type::Named(_) => todo!(),
        }
    }

    fn convert_type_to_llvm_type(&self, typ: &Type) -> AnyTypeEnum<'ctx> {
        todo!()
    }

    fn create_parameter_type_list(
        &mut self,
        param_list: &Vec<ast::NameTypeBind>,
    ) -> Vec<BasicMetadataTypeEnum<'ctx>> {
        todo!()
    }

    fn create_function(&mut self, func_def: &ast::FuncDef) {
        let ast::FuncDef {
            name,
            param_list,
            body,
            ret_type,
        } = func_def;

        let void_ty = self.context.void_type();
        let fn_ty = void_ty.fn_type(&self.create_parameter_type_list(param_list)[..], false);
        self.module.add_function(name, fn_ty, None);
        self.push_symbol(name);
    }

    fn emit_code(&mut self, module: &ast::Module) {
        module
            .imports
            .iter()
            .for_each(|ref_path| self.create_import(ref_path));

        module
            .data_defs
            .iter()
            .for_each(|data_def| self.create_data_type(data_def));

        module
            .func_defs
            .iter()
            .for_each(|func_def| self.create_function(func_def));
    }
}

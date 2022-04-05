use crate::ast::{self, LetStmt, NameTypeBind};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum, PointerType, StructType};
use inkwell::values::FunctionValue;
use inkwell::{memory_buffer, AddressSpace};
use std::collections::HashMap;
use std::path::Path;
use std::vec;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum Type {
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Enum(Vec<Option<Type>>),
    Unit,
}

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    sym_scope: Vec<HashMap<String, ()>>,
    fn_env: HashMap<String, FunctionValue<'ctx>>,
    ty_env: HashMap<String, Type>,
    ty_pool: HashMap<Type, StructType<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
    fn new(name: &'ctx str, context: &'ctx Context) -> Self {
        let module = context.create_module(name);
        let builder = context.create_builder();
        CodeGen {
            context,
            module,
            builder,
            fn_env: Default::default(),
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
        let set = self.sym_scope.last_mut().unwrap();
        set.insert(sym_name.clone(), ());
    }

    fn push_fn(&mut self, fn_name: String, fn_val: FunctionValue<'ctx>) {
        if self.fn_env.contains_key(&fn_name) {
            panic!("function `{}` redefined", fn_name)
        }
        self.fn_env.insert(fn_name, fn_val);
    }

    fn get_fn(&self, fn_name: &str) -> &FunctionValue<'ctx> {
        if !self.fn_env.contains_key(fn_name) {
            panic!("function `{}` not defined", fn_name)
        }
        self.fn_env.get(fn_name).unwrap()
    }

    fn get_fn_mut(&mut self, fn_name: &str) -> &mut FunctionValue<'ctx> {
        if !self.fn_env.contains_key(fn_name) {
            panic!("function `{}` not defined", fn_name)
        }
        self.fn_env.get_mut(fn_name).unwrap()
    }

    fn create_import(&mut self, ref_path: &ast::RefPath) {}

    fn create_data_type(&mut self, date_def: &ast::DataDef) {
        let ast::DataDef { name, con_list } = date_def;
        if self.ty_env.contains_key(name) {
            panic!("data type redefined")
        }
        let typ = self.convert_ast_type_to_type(con_list);
        self.ty_env.insert(name.to_string(), typ);
    }

    fn convert_ast_type_to_type(&self, typ: &ast::Type) -> Type {
        match typ {
            ast::Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.convert_ast_type_to_type(a)),
                Box::new(self.convert_ast_type_to_type(b)),
            ),
            ast::Type::Tuple(v) => {
                Type::Tuple(v.iter().map(|x| self.convert_ast_type_to_type(x)).collect())
            }
            ast::Type::Enum(v) => Type::Enum(
                v.iter()
                    .map(|x| x.inner.as_ref().map(|y| self.convert_ast_type_to_type(y)))
                    .collect(),
            ),
            ast::Type::Unit => Type::Unit,
            ast::Type::Named(s) => self
                .ty_env
                .get(s)
                .map_or_else(
                    || panic!("cannot found type {} in the type environment", s),
                    |x| x,
                )
                .clone(),
        }
    }

    fn get_enum_member_size(&self, member: &Option<Type>) -> u64 {
        let size = member.as_ref().map(|t| {
            self.get_llvm_type(t)
                .size_of()
                .unwrap()
                .get_zero_extended_constant()
                .unwrap_or(0)
        });
        size.unwrap_or(0)
    }

    fn get_boxed_type(&self, typ: StructType<'ctx>) -> PointerType<'ctx> {
        typ.ptr_type(AddressSpace::Generic)
    }

    fn convert_type_to_llvm_type(&mut self, typ: &Type) -> StructType<'ctx> {
        match typ {
            Type::Arrow(_, _) => todo!(),
            Type::Tuple(elem) => {
                // assure all llvm_types correspond to the code gen types has been generated
                // so that we don't need to borrow it mutably in later code
                elem.iter().for_each(|t| {
                    self.get_llvm_type_or_insert(t);
                });

                let fields: Vec<BasicTypeEnum> = elem
                    .iter()
                    .map(|t| BasicTypeEnum::StructType(self.get_llvm_type(t)))
                    .collect();

                self.context.struct_type(&fields[..], false)
            }
            Type::Enum(opt) => {
                // assure all llvm_types correspond to the code gen types has been generated
                // so that we don't need to borrow it mutably in later code
                opt.iter().for_each(|x| {
                    if let Some(t) = x {
                        self.get_llvm_type_or_insert(t);
                    }
                });

                // get the max size member of an enumeration
                let max_size_member = opt.iter().max_by(|&x, &y| {
                    self.get_enum_member_size(x)
                        .cmp(&self.get_enum_member_size(y))
                });

                // tag field, it's a 32-bit width integer
                let mut fields = vec![BasicTypeEnum::IntType(self.context.i32_type())];

                // max size element as the only field (llvm has no union type)
                if let Some(Some(member)) = max_size_member {
                    fields.push(BasicTypeEnum::StructType(self.get_llvm_type(member)));
                }

                self.context.struct_type(&fields[..], false)
            }
            Type::Unit => self.context.struct_type(&[], false),
        }
    }

    fn add_runtime_function(&mut self) {
        let memory_buffer =
            MemoryBuffer::create_from_file(Path::new("calocom_runtime.ll")).unwrap();
        let runtime_module = self.context.create_module_from_ir(memory_buffer).unwrap();
        self.module.link_in_module(runtime_module).unwrap()
    }

    fn get_llvm_type_or_insert(&mut self, typ: &Type) -> StructType<'ctx> {
        if !self.ty_pool.contains_key(typ) {
            let llvm_type = self.convert_type_to_llvm_type(typ);
            self.ty_pool.insert(typ.clone(), llvm_type);
        }
        self.get_llvm_type(typ)
    }

    fn get_llvm_type(&self, typ: &Type) -> StructType<'ctx> {
        *self.ty_pool.get(typ).unwrap()
    }

    fn create_parameter_type_list(
        &mut self,
        param_list: &[ast::NameTypeBind],
    ) -> Vec<BasicMetadataTypeEnum<'ctx>> {
        param_list
            .iter()
            .map(
                |NameTypeBind {
                     with_at,
                     var_name: _,
                     typ,
                 }| {
                    let typ = self.convert_ast_type_to_type(typ);
                    let raw_struct_type = self.get_llvm_type_or_insert(&typ);
                    let mut llvm_type = self.get_boxed_type(raw_struct_type);
                    if *with_at {
                        llvm_type = llvm_type.ptr_type(AddressSpace::Generic);
                    }
                    BasicMetadataTypeEnum::PointerType(llvm_type)
                },
            )
            .collect()
    }

    fn create_function(&mut self, func_def: &ast::FuncDef) {
        self.entry_symbol_scope();
        let ast::FuncDef {
            name,
            param_list,
            body,
            ret_type,
        } = func_def;

        let ret_type = self.convert_ast_type_to_type(ret_type);
        let ret_type = self.get_llvm_type_or_insert(&ret_type);
        let param_list_type = &self.create_parameter_type_list(param_list)[..];
        let fn_ty = ret_type.fn_type(param_list_type, false);
        let fn_val = self.module.add_function(name, fn_ty, None);
        self.push_fn(name.clone(), fn_val);
        self.push_symbol(&name.clone());
        self.emit_body(fn_val, body);
        self.exit_symbol_scope();
    }

    fn emit_body_initial(&mut self, function: FunctionValue) {
        let entry_bb = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_bb);
    }

    fn emit_body(&mut self, function: FunctionValue, body: &ast::BracketBody) {
        self.emit_body_initial(function);
        body.stmts.iter().for_each(|stmt| self.emit_stmt(stmt));
        if let Some(expr) = &body.ret_expr {
            self.emit_expr(expr)
        }
    }

    fn create_stack_alloca(&mut self, name: &str, typ: &Type) {
        todo!()
    }

    fn allocate_default_object(&mut self) {
        todo!()
    }

    fn emit_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Let(l) => self.emit_let(l),
            ast::Stmt::Asgn(_) => todo!(),
            ast::Stmt::Expr(e) => self.emit_expr(e),
        }
    }

    fn emit_let(&mut self, stmt: &ast::LetStmt) {
        let LetStmt {
            var_name,
            typ,
            expr,
        } = stmt;

        self.push_symbol(var_name);
    }

    fn emit_asgn(&mut self, stmt: &ast::AsgnStmt) {}

    fn emit_expr(&mut self, expr: &ast::Expr) {
        todo!()
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

#[cfg(test)]
mod tests {
    use inkwell::{context::Context, execution_engine};

    use super::*;
    use crate::frontend;
    use std::fs;

    #[test]
    fn test_codegen() {
        let context = Context::create();
        let name = "test";
        let mut codegen = CodeGen::new(name, &context);

        let s = fs::read_to_string("./example/stage1/at.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        codegen.emit_code(&ast);
    }
}

use crate::ast::{
    self, ArithExpr, BracketBody, CallExpr, Expr, LetStmt, Literal, MatchExpr, NameTypeBind,
};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum, PointerType, StructType};
use inkwell::values::PointerValue;
use inkwell::values::{BasicValue, FunctionValue, GlobalValue};
use inkwell::AddressSpace;
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
    sym_scope: Vec<HashMap<String, PointerValue<'ctx>>>,
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

    fn push_symbol(&mut self, sym_name: &String, sym_value: PointerValue<'ctx>) {
        let set = self.sym_scope.last_mut().unwrap();
        set.insert(sym_name.clone(), sym_value);
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
                    .map(|t| self.get_llvm_type(t).ptr_type(AddressSpace::Generic).into())
                    .collect();

                self.context.struct_type(&fields[..], false)
            }
            Type::Enum(opt) => {
                let fields: &[BasicTypeEnum] = &[
                    self.context.i32_type().into(),
                    self.context.i8_type().ptr_type(AddressSpace::Generic).into(),
                ];

                self.context.struct_type(fields, false)
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
                    llvm_type.into()
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
            self.emit_expr(expr.as_ref());
        }
    }

    fn emit_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Let(l) => self.emit_let(l),
            ast::Stmt::Asgn(_) => todo!(),
            ast::Stmt::Expr(e) => {
                self.emit_expr(e);
            }
        }
    }

    fn emit_let(&mut self, stmt: &ast::LetStmt) {
        let LetStmt {
            var_name,
            typ,
            expr,
        } = stmt;

        let result = self.emit_expr(expr);
        self.push_symbol(var_name, result);
    }

    fn emit_asgn(&mut self, stmt: &ast::AsgnStmt) {}

    fn get_unit_value() -> PointerValue<'ctx> {
        todo!()
    }

    fn emit_block_stmt(&mut self, body: &BracketBody) -> PointerValue<'ctx> {
        for stmt in &body.stmts {
            self.emit_stmt(stmt);
        }
        if let Some(ret_expr) = &body.ret_expr {
            self.emit_expr(ret_expr);
        }
        todo!()
    }

    fn emit_call_expr(&mut self, call: &CallExpr) -> PointerValue<'ctx> {
        todo!()
    }

    fn emit_arith_expr(&mut self, arith: &ArithExpr) -> PointerValue<'ctx> {
        todo!()
    }

    fn emit_match_expr(&mut self, expr: &MatchExpr) -> PointerValue<'ctx> {
        todo!()
    }

    fn emit_variable(&mut self, var: &String) -> PointerValue<'ctx> {
        todo!()
    }

    fn emit_runtime_alloc_object(&mut self, size: usize) -> PointerValue<'ctx> {
        self.builder
            .build_call(
                self.module
                    .get_function("__calocom_runtime_alloc_object")
                    .unwrap(),
                &[self
                    .context
                    .i64_type()
                    .const_int(size.try_into().unwrap(), false)
                    .into()],
                "",
            )
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value()
    }

    fn emit_constant_string_literal(&mut self, data: &String) -> PointerValue<'ctx> {
        let mut v = vec![];
        for i in data.bytes() {
            v.push(self.context.i8_type().const_int(i as u64, false));
        }
        let init = self.context.i8_type().const_array(&v[..]);
        let gv = self
            .module
            .add_global(init.get_type(), Some(AddressSpace::Generic), "");
        gv.set_constant(true);
        gv.set_initializer(&init.as_basic_value_enum());
        gv.as_pointer_value()
    }

    fn emit_runtime_alloc_string_literal(&mut self, data: &String) -> PointerValue<'ctx> {
        let size = data.as_bytes().len();
        let gvp = self.emit_constant_string_literal(data);
        self.builder
            .build_call(
                self.module
                    .get_function("__calocom_runtime_alloc_string_literal")
                    .unwrap(),
                &[
                    self.context
                        .i64_type()
                        .const_int(size.try_into().unwrap(), false)
                        .into(),
                    gvp.into(),
                ],
                "",
            )
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value()
    }

    fn emit_literal(&mut self, lit: &Literal) -> PointerValue<'ctx> {
        match lit {
            Literal::Int(i) => {
                let local = self
                    .builder
                    .build_alloca(self.context.i32_type().ptr_type(AddressSpace::Generic), "");

                let alloc = self.emit_runtime_alloc_object(std::mem::size_of::<i32>());
                self.builder.build_store(local, alloc);

                let loaded = self.builder.build_load(local, "");
                self.builder.build_store(
                    loaded.into_pointer_value(),
                    self.context.i32_type().const_int(*i as u64, false),
                );

                return self.builder.build_load(local, "").into_pointer_value();
            }

            Literal::Str(s) => {
                todo!()
            }

            Literal::Bool(b) => {
                let local = self
                    .builder
                    .build_alloca(self.context.bool_type().ptr_type(AddressSpace::Generic), "");

                let alloc = self.emit_runtime_alloc_object(std::mem::size_of::<bool>());
                self.builder.build_store(local, alloc);

                let loaded = self.builder.build_load(local, "");
                self.builder.build_store(
                    loaded.into_pointer_value(),
                    self.context.bool_type().const_int(*b as u64, true),
                );

                return self.builder.build_load(local, "").into_pointer_value();
            }
        };
        todo!()
    }

    fn emit_expr(&mut self, expr: &ast::Expr) -> PointerValue<'ctx> {
        match expr {
            Expr::BraExpr(body) => self.emit_block_stmt(body),
            Expr::CallExpr(call) => self.emit_call_expr(call),
            Expr::ArithExpr(arith) => self.emit_arith_expr(arith),
            Expr::MatchExpr(expr) => self.emit_match_expr(expr),
            Expr::Var(var) => self.emit_variable(var),
            Expr::Lit(lit) => self.emit_literal(lit),
        }
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

        let s = fs::read_to_string("./example/stage1/hello_world.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        codegen.emit_code(&ast);
    }
}

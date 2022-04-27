use std::{collections::HashMap, panic, vec};

use super::type_context::*;
use crate::sym::SymbolTable;

#[derive(Debug)]
pub struct TypedFuncDef {
    pub name: String,
    pub param_list: Vec<TypedBind>,
    pub ret_type: usize,
    pub body: Box<TypedBracketBody>,
}

#[derive(Debug)]
pub struct TypedBind {
    pub with_at: bool,
    pub var_name: String,
    pub typ: usize,
}

#[derive(Debug)]
pub struct TypedBracketBody {
    pub stmts: Vec<TypedASTStmt>,
    pub ret_expr: Option<TypedExpr>,
    pub typ: usize,
}

#[derive(Debug)]
pub struct TypedLetStmt {
    pub var_name: String,
    pub var_typ: usize,
    pub expr: TypedExpr,
}

#[derive(Debug)]
pub struct TypedAsgnStmt {
    pub var_name: String,
    pub var_typ: usize,
    pub expr: TypedExpr,
}

#[derive(Debug)]
pub enum TypedASTStmt {
    Let(Box<TypedLetStmt>),
    Asgn(Box<TypedAsgnStmt>),
    Expr(Box<TypedExpr>),
}

#[derive(Debug)]
pub struct TypedCallExpr {
    pub path: TypedASTRefPath,
    pub gen: Option<Type>, // generic notation
    pub args: Vec<TypedArgument>,
}

#[derive(Debug)]
pub struct TypedArithExpr {
    pub lhs: TypedExpr,
    pub rhs: TypedExpr,
    pub op: TypedASTBinOp,
    pub typ: usize,
}

#[derive(Debug)]
pub struct TypedMatchExpr {
    pub e: TypedExpr,
    pub arms: Vec<(Pattern, TypedExpr)>,
    pub typ: usize,
}

#[derive(Debug)]
pub struct TypedExpr {
    pub expr: Box<ExprEnum>,
    pub typ: usize,
}

#[derive(Debug)]
pub struct TypedCtorExpr {
    pub typ: usize,
    pub name: String,
    pub args: Vec<TypedArgument>,
}

#[derive(Debug)]
pub enum ExprEnum {
    BraExpr(TypedBracketBody),
    CallExpr(TypedCallExpr),
    ArithExpr(TypedArithExpr),
    MatchExpr(TypedMatchExpr),
    CtorExpr(TypedCtorExpr),
    Var(String),
    Lit(TypedASTLiteral),
}

#[derive(Debug)]
pub enum Pattern {
    Lit(TypedASTLiteral),
    Con(TypedASTConstructorVar),
}

#[derive(Debug)]
pub enum TypedArgument {
    Expr(TypedExpr),
    AtVar(String, usize),
}

#[derive(Debug)]
pub enum TypedASTBinOp {
    Plus,
    Sub,
    Mult,
    Div,
    Mod,
}

#[derive(Debug)]
pub enum TypedASTLiteral {
    Int(i32),
    Str(String),
    Bool(bool),
}

#[derive(Debug)]
pub struct TypedASTRefPath {
    pub items: Vec<String>,
}

impl From<&crate::ast::RefPath> for TypedASTRefPath {
    fn from(path: &crate::ast::RefPath) -> TypedASTRefPath {
        TypedASTRefPath {
            items: path.items.clone(),
        }
    }
}

#[derive(Debug)]
pub struct TypedASTConstructorVar {
    pub name: String,
    pub inner: Option<String>,
}

#[derive(Debug, Default)]
pub struct TypedAST {
    pub ty_ctx: TypeContext,
    pub imports: HashMap<String, TypedASTRefPath>,
    pub constructors: HashMap<String, usize>,
    pub module: Vec<TypedFuncDef>,
}

impl From<&crate::ast::BinOp> for TypedASTBinOp {
    fn from(op: &crate::ast::BinOp) -> Self {
        match op {
            crate::ast::BinOp::Plus => TypedASTBinOp::Plus,
            crate::ast::BinOp::Sub => TypedASTBinOp::Sub,
            crate::ast::BinOp::Mult => TypedASTBinOp::Mult,
            crate::ast::BinOp::Div => TypedASTBinOp::Div,
            crate::ast::BinOp::Mod => TypedASTBinOp::Mod,
        }
    }
}

impl From<&crate::ast::Literal> for TypedASTLiteral {
    fn from(lit: &crate::ast::Literal) -> Self {
        match lit {
            crate::ast::Literal::Int(i) => TypedASTLiteral::Int(*i),
            crate::ast::Literal::Str(s) => TypedASTLiteral::Str(s.clone()),
            crate::ast::Literal::Bool(b) => TypedASTLiteral::Bool(*b),
        }
    }
}

impl From<&crate::ast::Pattern> for Pattern {
    fn from(pat: &crate::ast::Pattern) -> Self {
        match pat {
            crate::ast::Pattern::Lit(lit) => Self::Lit(lit.into()),
            crate::ast::Pattern::Con(ctor_var) => Self::Con(TypedASTConstructorVar {
                name: ctor_var.name.clone(),
                inner: ctor_var.inner.clone(),
            }),
        }
    }
}

impl TypedAST {
    fn resolve_type_with_at(&mut self, ast_type: &crate::ast::Type) -> (usize, Type) {
        let (idx, _typ) = self.resolve_type(ast_type, false);

        self.ty_ctx.opaque_type(idx)
    }

    fn resolve_type(&mut self, ast_type: &crate::ast::Type, allow_opaque: bool) -> (usize, Type) {
        match ast_type {
            crate::ast::Type::Arrow(_, _) => unimplemented!(),

            crate::ast::Type::Tuple(tuple) => {
                let mut fields = vec![];
                for ty in tuple {
                    let (_, field) = self.resolve_type(ty, allow_opaque);
                    fields.push(field);
                }

                self.ty_ctx.tuple_type(fields)
            }

            crate::ast::Type::Enum(e) => {
                let mut ctors = vec![];

                for crate::ast::ConstructorType { name, inner } in e {
                    let ty = if inner.is_some() {
                        let (_, ty) = self.resolve_type(inner.as_ref().unwrap(), allow_opaque);
                        Some(ty)
                    } else {
                        None
                    };
                    ctors.push((name.clone(), ty));
                }

                self.ty_ctx.enum_type(ctors)
            }

            crate::ast::Type::Unit => self.ty_ctx.singleton_type(PrimitiveType::Unit),

            crate::ast::Type::Named(s) => {
                if let Some(handle) = self.ty_ctx.get_type_by_name(s) {
                    handle
                } else if allow_opaque {
                    self.ty_ctx.opaque_name_type(s)
                } else {
                    panic!("unresolved type: {}", s);
                }
            }
        }
    }

    fn resolve_all_type(&mut self, module: &crate::ast::Module) {
        for crate::ast::DataDef { name, con_list } in &module.data_defs {
            let (idx, _typ) = self.resolve_type(con_list, true);
            self.ty_ctx.associate_name_and_idx(name, idx)
        }
    }

    fn resolve_import(&mut self, module: &crate::ast::Module) {
        let imports = &module.imports;
        for import in imports {
            let items = import.items.clone();
            let path = TypedASTRefPath { items };
            let name = path.items.last().expect("empty import").clone();
            if self.imports.contains_key(&name) {
                panic!(
                    "conflict import: {} and {}",
                    path.items.join("."),
                    self.imports.get(&name).unwrap().items.join(".")
                )
            }
            self.imports.insert(name, path);
        }
    }

    fn check_type(&mut self, module: &crate::ast::Module) {
        for func in &module.func_defs {
            self.check_type_of_function_signature(func)
        }
        for func in &module.func_defs {
            self.check_type_of_function(func)
        }
    }

    fn check_type_of_asgn(&mut self, stmt: &crate::ast::AsgnStmt) -> TypedAsgnStmt {
        let name = &stmt.var_name;
        let typ = *self
            .ty_ctx
            .env
            .find_symbol(name)
            .unwrap_or_else(|| panic!("variable undefined: {}", name));

        let typed_expr = self.check_type_of_expr(&stmt.expr);

        if !self.ty_ctx.is_compatible(typ, typed_expr.typ) {
            panic!("inconsistent type when assigning to {}", name);
        }

        TypedAsgnStmt {
            var_name: name.to_string(),
            var_typ: typ,
            expr: typed_expr,
        }
    }

    fn check_type_of_let(&mut self, stmt: &crate::ast::LetStmt) -> TypedLetStmt {
        let crate::ast::LetStmt {
            var_name,
            typ,
            expr,
        } = stmt;

        let (t, _) = self.resolve_type(typ, false);

        let typed_expr = self.check_type_of_expr(expr);

        if !self.ty_ctx.is_compatible(t, typed_expr.typ) {
            panic!("initializer of variable {} has incorrect type", var_name);
        }

        self.ty_ctx.env.insert_symbol(var_name.clone(), t);

        TypedLetStmt {
            var_name: var_name.to_string(),
            var_typ: t,
            expr: typed_expr,
        }
    }

    fn check_type_of_argument(&mut self, arg: &crate::ast::Argument) -> TypedArgument {
        match arg {
            crate::ast::Argument::Expr(e) => TypedArgument::Expr(self.check_type_of_expr(e)),
            crate::ast::Argument::AtVar(name) => {
                let typ = *self
                    .ty_ctx
                    .env
                    .find_symbol(name)
                    .unwrap_or_else(|| panic!("variable undefined: {}", name));

                TypedArgument::AtVar(name.to_string(), typ)
            }
        }
    }

    fn check_type_of_external_call(
        &mut self,
        path: &crate::ast::RefPath,
        gen: Option<Type>,
        typed_args: Vec<TypedArgument>,
    ) -> TypedExpr {
        let call_path = &mut path.items.clone();
        let mut full_path = self
            .imports
            .get(call_path.first().unwrap())
            .unwrap()
            .items
            .clone();
        full_path.pop();
        full_path.append(call_path);
        if let Some(ty) = self
            .ty_ctx
            .find_external_polymorphic_function_type(&full_path[..])
        {
            if ty.1.len() != typed_args.len() {
                panic!(
                    "wrong number of arguments: expect {} but given {}",
                    ty.1.len(),
                    typed_args.len()
                );
            }

            for (idx, (typ, typed_arg)) in ty.1.iter().zip(typed_args.iter()).enumerate() {
                match typed_arg {
                    TypedArgument::Expr(e) => {
                        if !self.ty_ctx.is_compatible(*typ, e.typ) {
                            panic!("argument {} type incorrect", idx);
                        }
                    }
                    TypedArgument::AtVar(_, atvar_typ) => {
                        if !self.ty_ctx.is_compatible(*typ, *atvar_typ) {
                            panic!("argument {} type incorrect", idx);
                        }
                    }
                }
            }

            let typed_call = TypedCallExpr {
                path: TypedASTRefPath { items: full_path },
                gen,
                args: typed_args,
            };

            TypedExpr {
                typ: ty.0,
                expr: Box::new(ExprEnum::CallExpr(typed_call)),
            }
        } else {
            panic!("not callable: {}", full_path.join(""));
        }
    }

    fn check_type_of_call(&mut self, call: &crate::ast::CallExpr) -> TypedExpr {
        let crate::ast::CallExpr { path, gen, args } = call;

        let first_item = &path.items[0];

        let args = args
            .iter()
            .map(|arg| self.check_type_of_argument(arg))
            .collect();

        // it's a constructor with arguments
        if path.items.len() == 1 {
            if let Some(&typ) = self.constructors.get(first_item) {
                let ctor_expr = TypedCtorExpr {
                    typ,
                    name: path.items[0].clone(),
                    args,
                };

                return TypedExpr {
                    typ,
                    expr: Box::new(ExprEnum::CtorExpr(ctor_expr)),
                };
            }
        }

        let new_generic = gen.as_ref().map(|ty| self.resolve_type(ty, false).1);

        if self.imports.contains_key(first_item) {
            return self.check_type_of_external_call(path, new_generic, args);
        }

        if let Some(ty) = self.ty_ctx.find_function_type(first_item) {
            if ty.1.len() != args.len() {
                panic!(
                    "wrong number of arguments: expect {} but given {}",
                    ty.1.len(),
                    args.len()
                );
            }

            for (idx, (typ, typed_arg)) in ty.1.iter().zip(args.iter()).enumerate() {
                match typed_arg {
                    TypedArgument::Expr(e) => {
                        if !self.ty_ctx.is_compatible(*typ, e.typ) {
                            panic!("argument {} type incorrect", idx);
                        }
                    }
                    TypedArgument::AtVar(_, atvar_typ) => {
                        if !self.ty_ctx.is_compatible(*typ, *atvar_typ) {
                            panic!("argument {} type incorrect", idx);
                        }
                    }
                }
            }

            let typed_call = TypedCallExpr {
                path: path.into(),
                gen: new_generic,
                args,
            };

            TypedExpr {
                typ: ty.0,
                expr: Box::new(ExprEnum::CallExpr(typed_call)),
            }
        } else {
            panic!("not callable: {}", first_item);
        }
    }

    fn check_type_of_var(&mut self, var: &str) -> TypedExpr {
        if let Some(&typ) = self.constructors.get(var) {
            let ctor_expr = TypedCtorExpr {
                typ,
                name: var.to_string(),
                args: vec![],
            };

            TypedExpr {
                typ,
                expr: Box::new(ExprEnum::CtorExpr(ctor_expr)),
            }
        } else {
            let typ = *self
                .ty_ctx
                .env
                .find_symbol(var)
                .unwrap_or_else(|| panic!("undefined variable: {}", var));

            TypedExpr {
                typ,
                expr: Box::new(ExprEnum::Var(var.to_string())),
            }
        }
    }

    fn check_type_of_match(&mut self, mexp: &crate::ast::MatchExpr) -> TypedExpr {
        let crate::ast::MatchExpr { e, arms } = mexp;
        let match_expr = self.check_type_of_expr(e);
        let mut typed_arms = vec![];
        for (pat, expr) in arms {
            match pat {
                crate::ast::Pattern::Lit(lit) => {
                    let typ = self.check_type_of_literal(lit).typ;
                    if self.ty_ctx.is_compatible(typ, match_expr.typ) {
                        typed_arms.push(self.check_type_of_expr(expr));
                    } else {
                        panic!("invalid literal for match arm: type is not compatible")
                    }
                }
                crate::ast::Pattern::Con(crate::ast::ConstructorVar { name, inner }) => {
                    if let Some(&typ) = self.constructors.get(name) {
                        if self.ty_ctx.is_compatible(typ, match_expr.typ) {
                            if let Some(bind) = inner {
                                let (typ, _) =
                                    self.ty_ctx.get_ctor_field_type_by_name(typ, name).unwrap();
                                self.ty_ctx.env.entry();
                                self.ty_ctx.env.insert_symbol(bind.to_string(), typ);
                                typed_arms.push(self.check_type_of_expr(expr));
                                self.ty_ctx.env.exit();
                            } else {
                                typed_arms.push(self.check_type_of_expr(expr));
                            }
                        } else {
                            panic!("invalid constructor for match arm: constructor belongs to another type")
                        }
                    } else {
                        panic!("invalid constructor for match arm: constructor doesn't exist")
                    };
                }
            }
        }

        let first_arm_typ = typed_arms.first().unwrap().typ;

        // requires same, because we don't expect to infer opaque type
        if !typed_arms.iter().all(|expr| expr.typ == first_arm_typ) {
            panic!("match arm returns incompatible types")
        }

        TypedExpr {
            typ: first_arm_typ,
            expr: Box::new(ExprEnum::MatchExpr(TypedMatchExpr {
                e: match_expr,
                arms: typed_arms
                    .into_iter()
                    .zip(arms)
                    .map(|(expr, (pat, _))| (pat.into(), expr))
                    .collect(),
                typ: first_arm_typ,
            })),
        }
    }

    fn check_type_of_literal(&mut self, lit: &crate::ast::Literal) -> TypedExpr {
        let lit: TypedASTLiteral = lit.into();

        let typ = match lit {
            TypedASTLiteral::Int(_) => self.ty_ctx.singleton_type(PrimitiveType::Int32),
            TypedASTLiteral::Str(_) => self.ty_ctx.singleton_type(PrimitiveType::Str),
            TypedASTLiteral::Bool(_) => self.ty_ctx.singleton_type(PrimitiveType::Bool),
        }
        .0;

        TypedExpr {
            typ,
            expr: Box::new(ExprEnum::Lit(lit)),
        }
    }

    fn check_type_of_expr(&mut self, expr: &crate::ast::Expr) -> TypedExpr {
        match expr {
            crate::ast::Expr::BraExpr(body) => {
                let expr = self.check_type_of_bracket_body(body);

                TypedExpr {
                    typ: expr.typ,
                    expr: Box::new(ExprEnum::BraExpr(expr)),
                }
            }
            crate::ast::Expr::CallExpr(call) => self.check_type_of_call(call),
            crate::ast::Expr::ArithExpr(exp) => {
                let crate::ast::ArithExpr { lhs, rhs, op } = exp;
                let left = self.check_type_of_expr(lhs);
                let right = self.check_type_of_expr(rhs);

                if !self.ty_ctx.is_compatible(left.typ, right.typ) {
                    panic!("invalid operator type");
                }

                let ty = left.typ;

                let tae = TypedArithExpr {
                    typ: ty,
                    lhs: left,
                    rhs: right,
                    op: op.into(),
                };

                TypedExpr {
                    typ: ty,
                    expr: Box::new(ExprEnum::ArithExpr(tae)),
                }
            }
            crate::ast::Expr::MatchExpr(m) => self.check_type_of_match(m),
            crate::ast::Expr::Var(var) => self.check_type_of_var(var),
            crate::ast::Expr::Lit(lit) => self.check_type_of_literal(lit),
        }
    }

    fn check_type_of_stmt(&mut self, stmt: &crate::ast::Stmt) -> TypedASTStmt {
        match stmt {
            crate::ast::Stmt::Let(stmt) => {
                TypedASTStmt::Let(Box::new(self.check_type_of_let(stmt)))
            }
            crate::ast::Stmt::Asgn(stmt) => {
                TypedASTStmt::Asgn(Box::new(self.check_type_of_asgn(stmt)))
            }
            crate::ast::Stmt::Expr(expr) => {
                TypedASTStmt::Expr(Box::new(self.check_type_of_expr(expr)))
            }
        }
    }

    fn check_type_of_bracket_body(&mut self, body: &crate::ast::BracketBody) -> TypedBracketBody {
        self.ty_ctx.env.entry();

        let typed_stmts = body
            .stmts
            .iter()
            .map(|stmt| self.check_type_of_stmt(stmt))
            .collect();

        let typed_expr = body
            .ret_expr
            .as_ref()
            .map(|expr| self.check_type_of_expr(expr));
        let typ = typed_expr.as_ref().map_or_else(
            || self.ty_ctx.singleton_type(PrimitiveType::Unit).0,
            |expr| expr.typ,
        );

        self.ty_ctx.env.exit();

        TypedBracketBody {
            stmts: typed_stmts,
            ret_expr: typed_expr,
            typ,
        }
    }

    fn check_type_of_function_signature(&mut self, func: &crate::ast::FuncDef) {
        let (t1, _) = self.resolve_type(&func.ret_type, false);

        let tps = func.param_list.iter().map(| crate::ast::NameTypeBind {
            with_at,
            var_name: _,
            typ, }
        | if !*with_at {
            self.resolve_type(typ, false)
        } else {
            self.resolve_type_with_at(typ)
        }.0).collect();

        self.ty_ctx
            .associate_function_type(func.name.as_str(), (t1, tps));
    }

    fn check_type_of_function(&mut self, func: &crate::ast::FuncDef) {
        let (declared_return_type, declared_param_types) = self
            .ty_ctx
            .find_function_type(func.name.as_str())
            .unwrap()
            .clone();
        self.ty_ctx.env.entry();
        let mut vec_param = vec![];

        for (
            idx,
            crate::ast::NameTypeBind {
                with_at,
                var_name,
                typ: _,
            },
        ) in func.param_list.iter().enumerate()
        {
            let tp = declared_param_types[idx];

            vec_param.push(TypedBind {
                with_at: *with_at,
                var_name: var_name.clone(),
                typ: tp,
            });

            self.ty_ctx.env.insert_symbol(var_name.to_string(), tp);
        }

        let body = self.check_type_of_bracket_body(&func.body);
        if !self.ty_ctx.is_compatible(body.typ, declared_return_type) {
            panic!("return type inconsistent: {}", func.name);
        }

        self.ty_ctx.env.exit();

        self.module.push(TypedFuncDef {
            name: func.name.to_string(),
            param_list: vec_param,
            ret_type: declared_return_type,
            body: Box::new(body),
        });
    }

    fn create_library_function_signature(&mut self) {
        let unit = self.ty_ctx.singleton_type(PrimitiveType::Unit).0;
        let object = self.ty_ctx.singleton_type(PrimitiveType::Object).0;
        self.ty_ctx.associate_external_polymorphic_function_type(
            &["std", "io", "print"].map(|s| s.to_string()),
            (unit, [object].into()),
        );
        self.ty_ctx.associate_external_polymorphic_function_type(
            &["std", "io", "println"].map(|s| s.to_string()),
            (unit, [object].into()),
        );
    }

    pub fn create_from_ast(module: &crate::ast::Module) -> Self {
        let mut typed_ast = TypedAST::default();

        typed_ast.create_library_function_signature();
        typed_ast.resolve_import(module);
        typed_ast.resolve_all_type(module);
        typed_ast.ty_ctx.refine_all_opaque_type();
        typed_ast
            .ty_ctx
            .collect_all_constructor(&mut typed_ast.constructors);
        typed_ast.check_type(module);

        typed_ast
    }
}

impl From<crate::ast::Module> for TypedAST {
    fn from(module: crate::ast::Module) -> Self {
        TypedAST::create_from_ast(&module)
    }
}

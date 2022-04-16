use std::{
    collections::{HashMap, HashSet},
    panic,
    rc::Rc,
    vec,
};

use crate::{ast::NameTypeBind, sym::SymbolTable};

use super::type_context::*;
use super::unique_name::UniqueName;

pub type SymTable<T> = Vec<HashMap<String, T>>;

#[derive(Debug, Default)]
pub struct Module {
    pub data_defs: Vec<DataDef>,
    pub func_defs: Vec<FuncDef>,
}

#[derive(Debug)]
pub struct RefPath {
    pub items: Vec<String>,
}

#[derive(Debug)]
pub struct DataDef {
    pub name: String,
    pub con_list: Type,
}

#[derive(Debug, Default)]
pub struct FuncDef {
    pub name: String,
    pub param_def: Vec<(bool, Rc<VarDef>)>,
    pub var_def: Vec<Rc<VarDef>>,
    pub tmp_def: Vec<Rc<VarDef>>,
    pub ret_def: Option<Rc<VarDef>>,
    pub blocks: Vec<Rc<Block>>,
}

#[derive(Debug)]
pub struct VarDef {
    pub name: String,
    pub typ: Type,
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

#[derive(Debug, Default)]
pub struct Stmt {
    pub left: Option<Rc<VarDef>>,
    pub right: Option<Value>,
    pub note: String,
}

#[derive(Debug)]
pub enum Terminator {
    Cond(Box<Value>, Rc<Block>, Rc<Block>),
    Select(Box<Value>, Vec<Rc<Block>>),
    Jump(Rc<Block>),
    Return,
}

#[derive(Debug)]
pub enum BinOp {
    Plus,
    Sub,
    Mult,
    Div,
    Mod,
}

impl From<&crate::ast::BinOp> for BinOp {
    fn from(op: &crate::ast::BinOp) -> Self {
        match op {
            crate::ast::BinOp::Plus => BinOp::Plus,
            crate::ast::BinOp::Sub => BinOp::Sub,
            crate::ast::BinOp::Mult => BinOp::Mult,
            crate::ast::BinOp::Div => BinOp::Div,
            crate::ast::BinOp::Mod => BinOp::Mod,
        }
    }
}

#[derive(Debug)]
pub enum Value {
    Call(RefPath, Box<Value>, Box<Value>),
    Op(BinOp, Box<Value>, Box<Value>),
    Imm(Literal),
    Intrinsic(String, Vec<Box<Value>>),
    VarRef(Rc<VarDef>),
}

#[derive(Debug)]
pub enum Literal {
    Int(i32),
    Str(String),
    Bool(bool),
}

impl From<&crate::ast::Literal> for Literal {
    fn from(lit: &crate::ast::Literal) -> Self {
        match lit {
            crate::ast::Literal::Int(i) => Literal::Int(*i),
            crate::ast::Literal::Str(s) => Literal::Str(s.clone()),
            crate::ast::Literal::Bool(b) => Literal::Bool(*b),
        }
    }
}

#[derive(Debug)]
struct FunctionBuilder<'a> {
    pub position: Option<Rc<Block>>,
    pub namer: UniqueName,
    pub table: SymTable<Rc<VarDef>>,
    pub func: &'a mut FuncDef,
}

#[derive(Debug, Default)]
pub struct MiddleIR {
    ty_ctx: TypeContext,
    imports: HashMap<String, RefPath>,
    constructors: HashSet<String>,
    module: Module,
}

impl MiddleIR {
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
            let path = RefPath { items };
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

    fn convert_asgn(&mut self, name: &str, expr: &crate::ast::Expr, builder: &mut FunctionBuilder) {
        self.convert_expr(expr, builder, Some(name));
    }

    fn convert_construction(&mut self) -> Value {
        todo!()
    }

    fn convert_expr(
        &mut self,
        expr: &crate::ast::Expr,
        builder: &mut FunctionBuilder,
        out: Option<&str>,
    ) {
        let mut stmt = Stmt::default();

        if let Some(name) = out {
            let var = builder
                .table
                .find_symbol(name)
                .expect("variable not defined");
            stmt.left = Some(Rc::clone(var));
        }

        stmt.right = Some(match expr {
            crate::ast::Expr::MatchExpr(_) => todo!(),
            crate::ast::Expr::BraExpr(_) => todo!(),
            crate::ast::Expr::CallExpr(_) => todo!(),
            crate::ast::Expr::ArithExpr(arith) => {
                todo!()
            }
            crate::ast::Expr::Var(name) => {
                if self.constructors.contains(name) {
                    self.convert_construction()
                } else {
                    Value::VarRef(Rc::clone(
                        builder
                            .table
                            .find_symbol(name)
                            .expect("variable not defined"),
                    ))
                }
            }
            crate::ast::Expr::Lit(lit) => Value::Imm(lit.into()),
        });
    }

    fn convert_let(&mut self, stmt: &crate::ast::LetStmt, builder: &mut FunctionBuilder) {
        let crate::ast::LetStmt {
            var_name,
            typ,
            expr,
        } = stmt;

        let name = builder.namer.next_name(var_name);
        let (_, typ) = self.resolve_type(typ, false);
        let new_var = Rc::new(VarDef { name, typ });

        builder
            .table
            .insert_symbol(var_name.clone(), Rc::clone(&new_var));
        builder.func.tmp_def.push(new_var);

        self.convert_asgn(var_name, expr, builder);
    }

    fn convert_stmt(&mut self, stmt: &crate::ast::Stmt, builder: &mut FunctionBuilder) {
        match stmt {
            crate::ast::Stmt::Let(stmt) => self.convert_let(stmt, builder),
            crate::ast::Stmt::Asgn(stmt) => self.convert_asgn(&stmt.var_name, &stmt.expr, builder),
            crate::ast::Stmt::Expr(stmt) => self.convert_expr(stmt, builder, None),
        }
    }

    fn convert_bracket_body(
        &mut self,
        body: &crate::ast::BracketBody,
        builder: &mut FunctionBuilder,
        out: Option<&str>,
    ) {
        for stmt in &body.stmts {
            self.convert_stmt(stmt, builder)
        }
        if let Some(ret_expr) = &body.ret_expr {
            self.convert_expr(ret_expr, builder, out);
        }
    }

    fn convert_fn_definition(&mut self, func: &crate::ast::FuncDef) -> FuncDef {
        let mut def = FuncDef {
            name: func.name.clone(),
            ..Default::default()
        };

        // setup the return type and create the return value variable
        let (_, typ) = self.resolve_type(&func.ret_type, false);
        let name = "#ret.ptr".to_string();
        let name_cpy = name.clone();
        let ret = Rc::new(VarDef { name, typ });
        def.ret_def = Some(ret.clone());

        // setup the symbol table
        // insert the return value variable
        let mut sym_table: SymTable<Rc<VarDef>> = SymTable::new();
        sym_table.entry();
        sym_table.insert_symbol(name_cpy, Rc::clone(&ret));

        // initialize all parameters
        for NameTypeBind {
            with_at,
            var_name,
            typ,
        } in &func.param_list
        {
            let (_, typ) = if *with_at {
                self.resolve_type(typ, false)
            } else {
                self.resolve_type_with_at(typ)
            };
            let name = format!("#{}", var_name);
            let name_cpy = name.clone();
            let param = Rc::new(VarDef { name, typ });

            // insert the parameter into symbol table
            sym_table.insert_symbol(name_cpy, Rc::clone(&param));
            def.param_def.push((*with_at, param));
        }

        // return block
        let ret_block = Rc::new(Block {
            terminator: Terminator::Return,
            stmts: vec![],
        });

        // add an empty entry block and set the insert point
        let entry_block = Rc::new(Block {
            terminator: Terminator::Jump(Rc::clone(&ret_block)),
            stmts: vec![],
        });

        let position = Rc::clone(&entry_block);

        def.blocks.push(entry_block);
        def.blocks.push(ret_block);

        let mut fn_builder = FunctionBuilder {
            func: &mut def,
            position: Some(position),
            namer: UniqueName::new(),
            table: SymTable::<Rc<VarDef>>::new(),
        };

        // convert the function body
        self.convert_bracket_body(&func.body, &mut fn_builder, Some("#ret.ptr"));

        // exit the symbol table scope
        sym_table.exit();
        def
    }

    fn convert_ast(&mut self, module: &crate::ast::Module) {
        for func in &module.func_defs {
            let new_def = self.convert_fn_definition(func);
            self.module.func_defs.push(new_def);
        }
    }

    pub fn create_from_ast(module: &crate::ast::Module) -> Self {
        let mut mir = MiddleIR::default();

        mir.resolve_import(module);
        mir.resolve_all_type(module);
        mir.ty_ctx.refine_all_opaque_type();
        mir.convert_ast(module);

        mir
    }
}

impl From<crate::ast::Module> for MiddleIR {
    fn from(module: crate::ast::Module) -> Self {
        MiddleIR::create_from_ast(&module)
    }
}

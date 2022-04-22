use std::{collections::HashMap, panic, rc::Rc, vec};

use crate::sym::SymbolTable;

use super::type_context::*;
use super::typed_ast::*;
use super::unique_name::*;

pub type SymTable<T> = Vec<HashMap<String, T>>;

type RefPath = TypedASTRefPath;

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

pub type BinOp = TypedASTBinOp;

#[derive(Debug)]
pub enum Value {
    Call(RefPath, Box<Value>, Box<Value>),
    Op(BinOp, Box<Value>, Box<Value>),
    Imm(Literal),
    Intrinsic(String, Vec<Box<Value>>),
    VarRef(Rc<VarDef>),
}

pub type Literal = TypedASTLiteral;

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
    constructors: HashMap<String, usize>,
    module: Vec<FuncDef>,
}

impl MiddleIR {
    fn convert_asgn(&mut self, name: &str, expr: &TypedExpr, builder: &mut FunctionBuilder) {
        self.convert_expr(expr, builder, Some(name));
    }

    fn convert_construction(&mut self) -> Value {
        todo!()
    }

    fn convert_expr(
        &mut self,
        expr: &TypedExpr,
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

        let TypedExpr { expr, typ } = expr;
        stmt.right = Some(match **expr {
            ExprEnum::MatchExpr(_) => todo!(),
            ExprEnum::BraExpr(_) => todo!(),
            ExprEnum::CallExpr(_) => todo!(),
            ExprEnum::ArithExpr(_) => todo!(),
            ExprEnum::CtorExpr(_) => todo!(),
            ExprEnum::Var(_) => todo!(),
            ExprEnum::Lit(_) => todo!(),
        });
    }

    fn convert_let(&mut self, stmt: &TypedLetStmt, builder: &mut FunctionBuilder) {
        let TypedLetStmt {
            var_name,
            var_typ,
            expr,
        } = stmt;

        let name = builder.namer.next_name(var_name);
        let typ = self.ty_ctx.get_type_by_idx(*var_typ).1;
        let new_var = Rc::new(VarDef { name, typ });

        builder
            .table
            .insert_symbol(var_name.clone(), Rc::clone(&new_var));
        builder.func.tmp_def.push(new_var);

        self.convert_asgn(var_name, expr, builder);
    }

    fn convert_stmt(&mut self, stmt: &TypedASTStmt, builder: &mut FunctionBuilder) {
        match stmt {
            TypedASTStmt::Let(stmt) => self.convert_let(stmt, builder),
            TypedASTStmt::Asgn(stmt) => self.convert_asgn(&stmt.var_name, &stmt.expr, builder),
            TypedASTStmt::Expr(stmt) => self.convert_expr(stmt, builder, None),
        }
    }

    fn convert_bracket_body(
        &mut self,
        body: &TypedBracketBody,
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

    fn convert_fn_definition(&mut self, func: &TypedFuncDef) -> FuncDef {
        let mut def = FuncDef {
            name: func.name.clone(),
            ..Default::default()
        };

        // create the return value variable
        let (_, typ) = self.ty_ctx.get_type_by_idx(func.ret_type);
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
        for TypedBind {
            with_at,
            var_name,
            typ,
        } in &func.param_list
        {
            let typ = self.ty_ctx.get_type_by_idx(*typ).1;
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

    fn convert_ast(&mut self, fn_def: &Vec<TypedFuncDef>) {
        for func in fn_def {
            let new_def = self.convert_fn_definition(func);
            self.module.push(new_def);
        }
    }

    pub fn create_from_ast(ty_ast: TypedAST) -> Self {
        let TypedAST {
            ty_ctx,
            imports,
            constructors,
            module,
        } = ty_ast;

        let mut mir = MiddleIR {
            ty_ctx,
            imports,
            constructors,
            ..Default::default()
        };

        mir.convert_ast(&module);

        mir
    }
}

impl From<TypedAST> for MiddleIR {
    fn from(ty_ast: TypedAST) -> Self {
        MiddleIR::create_from_ast(ty_ast)
    }
}

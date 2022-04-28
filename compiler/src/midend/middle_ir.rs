use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::format;
use std::rc::Rc;
use std::{collections::HashMap, panic, vec};

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
    pub var_def: Vec<Rc<VarDef>>, // represents a reference to a local stack slot
    pub tmp_def: Vec<Rc<VarDef>>, // be the same as var_def but it's not named by users
    pub mem_ref: HashSet<Rc<VarDef>>, // only represents a reference to a memory position
    pub ret_def: Option<Rc<VarDef>>, // represents the reference to the stack slot where the return value locates
    pub blocks: Vec<Rc<RefCell<Block>>>,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct VarDef {
    pub name: String,
    pub typ: usize,
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
    Jump(Rc<RefCell<Block>>),
    Return,
}

pub type BinOp = TypedASTBinOp;

#[derive(Debug)]
pub enum Value {
    Call(RefPath, Vec<Value>),
    Op(BinOp, Box<Value>, Box<Value>),
    Imm(Literal),
    Intrinsic(&'static str, Vec<Value>),
    VarRef(Rc<VarDef>),
}

pub type Literal = TypedASTLiteral;

#[derive(Debug)]
struct FunctionBuilder<'a> {
    pub position: Option<Rc<RefCell<Block>>>,
    pub namer: UniqueName,
    pub table: SymTable<Rc<VarDef>>,
    pub func: &'a mut FuncDef,
}

#[derive(Debug, Default)]
pub struct MiddleIR {
    ty_ctx: TypeContext,
    module: Vec<FuncDef>,
}

impl MiddleIR {
    fn convert_asgn(&mut self, name: &str, expr: &TypedExpr, builder: &mut FunctionBuilder) {
        let var = Rc::clone(
            builder
                .table
                .find_symbol(name)
                .unwrap_or_else(|| panic!("variable {} not defined", name)),
        );
        self.convert_expr(expr, builder, Some(var));
    }

    fn convert_args(
        &mut self,
        builder: &mut FunctionBuilder,
        arg: &Vec<TypedArgument>,
        param: &Vec<usize>,
    ) -> Vec<Value> {
        todo!()
    }

    fn convert_ctor_expr(&mut self, builder: &mut FunctionBuilder, x: &TypedCtorExpr) -> Value {
        let TypedCtorExpr { typ, name, args } = x;
        let params_typ = self.ty_ctx.get_ctor_field_type_by_name(*typ, name);
        let mut args_value = self.convert_args(
            builder,
            args,
            &params_typ.iter().map(|(ty, _)| *ty).collect(),
        );
        let mut v = vec![Value::Imm(Literal::Str(name.clone()))];
        v.append(&mut args_value);
        Value::Intrinsic("calocom.construct", v)
    }

    fn convert_match_expr(&mut self, x: &TypedMatchExpr) -> Value {
        let TypedMatchExpr { e, arms, typ } = x;

        todo!()
    }

    fn convert_call_expr(&mut self, builder: &mut FunctionBuilder, x: &TypedCallExpr) -> Value {
        let TypedCallExpr { path, gen:_, args } = x;
        let params_typ = &self.ty_ctx.find_function_type(&path.items[0]).unwrap().1.clone();
        let args_value = self.convert_args(builder, args, params_typ);
        Value::Call(path.clone(), args_value)
    }

    fn convert_ext_call_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedExternalCallExpr,
    ) -> Value {
        let TypedExternalCallExpr { path, gen: _, args } = x;
        let params_typ = &self.ty_ctx.find_external_polymorphic_function_type(&path.items).unwrap().1.clone();
        let args_value = self.convert_args(builder, args, params_typ);
        Value::Call(path.clone(), args_value)
    }

    fn convert_bracket_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedBracketBody,
    ) -> Value {
        let TypedBracketBody {
            stmts,
            ret_expr,
            typ,
        } = x;
        builder.table.entry();

        let bracket_out = self.create_variable_definition("bracket.out", *typ);

        for stmt in stmts {
            self.convert_stmt(stmt, builder)
        }

        if let Some(ret_expr) = ret_expr {
            self.convert_expr(ret_expr, builder, Some(Rc::clone(&bracket_out)));
        }

        builder.table.exit();
        Value::VarRef(bracket_out)
    }

    fn convert_arith_expr(&mut self, builder: &mut FunctionBuilder, x: &TypedArithExpr) -> Value {
        let TypedArithExpr { lhs, rhs, op, typ } = x;

        let lhs_out = self.create_variable_definition("arith.lhs", *typ);
        let rhs_out = self.create_variable_definition("arith.rhs", *typ);

        builder.func.tmp_def.push(Rc::clone(&lhs_out));
        builder.func.tmp_def.push(Rc::clone(&rhs_out));

        self.convert_expr(lhs, builder, Some(Rc::clone(&lhs_out)));
        self.convert_expr(rhs, builder, Some(Rc::clone(&rhs_out)));

        Value::Op(
            op.clone(),
            Box::new(Value::VarRef(lhs_out)),
            Box::new(Value::VarRef(rhs_out)),
        )
    }

    fn convert_variable_expr(&mut self, builder: &mut FunctionBuilder, x: &str) -> Value {
        let var = builder
            .table
            .find_symbol(x)
            .unwrap_or_else(|| panic!("variable {} not defined", x));
        Value::VarRef(var.clone())
    }

    fn convert_literal_expr(&mut self, x: &Literal) -> Value {
        Value::Imm(x.clone())
    }

    fn create_value_from_expr(&mut self, builder: &mut FunctionBuilder, expr: &ExprEnum) -> Value {
        match expr {
            ExprEnum::MatchExpr(x) => self.convert_match_expr(x),
            ExprEnum::BraExpr(x) => self.convert_bracket_expr(builder, x),
            ExprEnum::CallExpr(x) => self.convert_call_expr(builder, x),
            ExprEnum::ExtCallExpr(x) => self.convert_ext_call_expr(builder, x),
            ExprEnum::ArithExpr(x) => self.convert_arith_expr(builder, x),
            ExprEnum::CtorExpr(x) => self.convert_ctor_expr(builder, x),
            ExprEnum::Var(x) => self.convert_variable_expr(builder, x.as_str()),
            ExprEnum::Lit(x) => self.convert_literal_expr(x),
        }
    }

    fn create_unboxed_value(
        &self,
        func: &mut FuncDef,
        namer: &mut UniqueName,
        name: &str,
        typ: usize,
    ) -> Rc<VarDef> {
        let name = namer.next_name(name);
        let base_type: Opaque = self.ty_ctx.get_type_by_idx(typ).1.into();
        let unboxed =
            self.create_variable_definition(name.as_str(), base_type.refer.left().unwrap());
        func.mem_ref.insert(Rc::clone(&unboxed));
        unboxed
    }

    fn convert_expr(
        &mut self,
        expr: &TypedExpr,
        builder: &mut FunctionBuilder,
        out: Option<Rc<VarDef>>,
    ) {
        let mut stmt = Stmt::default();

        let TypedExpr { expr, typ } = expr;
        let val = self.create_value_from_expr(builder, expr);
        let insert_position = &mut builder.position.as_ref().unwrap().borrow_mut().stmts;
        if let Some(lhs) = out {
            let t1 = lhs.typ;
            let t2 = *typ;

            if !self.ty_ctx.is_type_pure_eq(t1, t2) {
                if self.ty_ctx.is_object_type(t1) {
                    stmt.left = Some(Rc::clone(&lhs));
                    stmt.right = Some(Value::Intrinsic("calocom.erase_type", vec![val]));
                } else if self.ty_ctx.is_object_type(t2) {
                    stmt.left = Some(Rc::clone(&lhs));
                    stmt.right = Some(Value::Intrinsic("calocom.specialize_type", vec![val]));
                } else if self.ty_ctx.is_t1_opaque_of_t2(t1, t2) {
                    let unboxed = self.create_unboxed_value(
                        builder.func,
                        &mut builder.namer,
                        format!("{}.unboxed", lhs.name).as_str(),
                        t1,
                    );
                    builder.func.tmp_def.push(Rc::clone(&unboxed));

                    let unbox_stmt = Stmt {
                        left: Some(Rc::clone(&unboxed)),
                        right: Some(Value::Intrinsic(
                            "calocom.unbox",
                            vec![Value::VarRef(Rc::clone(&lhs))],
                        )),
                        ..Default::default()
                    };

                    insert_position.push(unbox_stmt);

                    stmt.left = Some(unboxed);
                    stmt.right = Some(val);
                } else if self.ty_ctx.is_t1_opaque_of_t2(t2, t1) {
                    let unboxed = self.create_unboxed_value(
                        builder.func,
                        &mut builder.namer,
                        "expr.unboxed",
                        t2,
                    );
                    builder.func.tmp_def.push(Rc::clone(&unboxed));

                    let unbox_stmt = Stmt {
                        left: Some(Rc::clone(&unboxed)),
                        right: Some(val),
                        ..Default::default()
                    };

                    insert_position.push(unbox_stmt);

                    stmt.left = Some(Rc::clone(&lhs));
                    stmt.right = Some(Value::VarRef(unboxed));
                } else if self.ty_ctx.is_type_opaque_eq(t1, t2) {
                    let unboxed1 = self.create_unboxed_value(
                        builder.func,
                        &mut builder.namer,
                        format!("{}.unboxed", lhs.name).as_str(),
                        t1,
                    );

                    let unboxed2 = self.create_unboxed_value(
                        builder.func,
                        &mut builder.namer,
                        "expr.unboxed",
                        t2,
                    );

                    let unbox_rhs = Stmt {
                        left: Some(Rc::clone(&unboxed2)),
                        right: Some(val),
                        ..Default::default()
                    };

                    let unbox_lhs = Stmt {
                        left: Some(Rc::clone(&unboxed1)),
                        right: Some(Value::Intrinsic(
                            "calocom.unbox",
                            vec![Value::VarRef(Rc::clone(&lhs))],
                        )),
                        ..Default::default()
                    };

                    builder.func.tmp_def.push(Rc::clone(&unboxed1));
                    builder.func.tmp_def.push(Rc::clone(&unboxed2));

                    insert_position.push(unbox_lhs);
                    insert_position.push(unbox_rhs);

                    stmt.left = Some(unboxed1);
                    stmt.right = Some(Value::VarRef(unboxed2));
                } else {
                    unreachable!()
                }
            }
        } else {
            stmt.right = Some(val);
        }

        insert_position.push(stmt);
    }

    fn convert_let(&mut self, stmt: &TypedLetStmt, builder: &mut FunctionBuilder) {
        let TypedLetStmt {
            var_name,
            var_typ,
            expr,
        } = stmt;

        let name = builder.namer.next_name(var_name);
        let new_var = self.create_variable_definition(name.as_str(), *var_typ);

        builder
            .table
            .insert_symbol(var_name.clone(), Rc::clone(&new_var));
        builder.func.var_def.push(new_var);

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
        out: Option<Rc<VarDef>>,
    ) {
        for stmt in &body.stmts {
            self.convert_stmt(stmt, builder)
        }
        if let Some(ret_expr) = &body.ret_expr {
            self.convert_expr(ret_expr, builder, out);
        }
    }

    fn create_variable_definition(&self, name: &str, typ: usize) -> Rc<VarDef> {
        let name = name.to_string();
        Rc::new(VarDef { name, typ })
    }

    fn convert_fn_definition(&mut self, func: &TypedFuncDef) -> FuncDef {
        let mut def = FuncDef {
            name: func.name.clone(),
            ..Default::default()
        };

        // create the return value variable
        let ret_name = "#ret.var".to_string();
        let ret = self.create_variable_definition(ret_name.as_str(), func.ret_type);
        def.ret_def = Some(ret.clone());

        // setup the symbol table
        // insert the return value variable
        let mut sym_table: SymTable<Rc<VarDef>> = SymTable::new();
        sym_table.entry();
        sym_table.insert_symbol(ret_name, Rc::clone(&ret));

        // initialize all parameters
        for TypedBind {
            with_at,
            var_name,
            typ,
        } in &func.param_list
        {
            let name = format!("#{}", var_name);
            let param = self.create_variable_definition(name.as_str(), *typ);

            // insert the parameter into symbol table
            sym_table.insert_symbol(name, Rc::clone(&param));
            def.param_def.push((*with_at, param));
        }

        // return block
        let ret_block = Rc::new(RefCell::new(Block {
            terminator: Terminator::Return,
            stmts: vec![],
        }));

        // add an empty entry block and set the insert point
        let entry_block = Rc::new(RefCell::new(Block {
            terminator: Terminator::Jump(Rc::clone(&ret_block)),
            stmts: vec![],
        }));

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
        self.convert_bracket_body(&func.body, &mut fn_builder, Some(Rc::clone(&ret)));

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
            imports: _,
            constructors: _,
            module,
        } = ty_ast;

        let mut mir = MiddleIR {
            ty_ctx,
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
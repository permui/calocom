use std::cell::RefCell;
use std::fmt::Display;
use std::rc::Rc;
use std::{collections::HashMap, panic, vec};

use crate::sym::SymbolTable;

use super::type_context::*;
use super::typed_ast::*;
use super::unique_name::*;

pub type SymTable<T> = Vec<HashMap<String, T>>;
type RefPath = TypedASTRefPath;

#[derive(Debug, Default, Clone)]
pub struct FuncDef {
    pub name: String,
    pub param_def: Vec<Rc<VarDef>>,
    pub var_def: Vec<Rc<VarDef>>, // represents a local stack slot containing a pointer to a object
    pub tmp_def: Vec<Rc<VarDef>>, // be the same as var_def but it's not named by users
    pub mem_ref: Vec<Rc<VarDef>>, // only represents a local stack slot containing a ptr to a ptr to a object
    pub unwrapped_def: Vec<Rc<VarDef>>, // represents a local slot for unwrapped value
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
    pub name: String,
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

impl Block {
    fn new(namer: &mut UniqueName, stmts: Vec<Stmt>, terminator: Terminator) -> Self {
        Block {
            name: namer.next_name("block"),
            stmts,
            terminator,
        }
    }
}

#[derive(Debug, Default)]
pub struct Stmt {
    pub left: Option<Rc<VarDef>>,
    pub right: Option<TypedValue>,
    pub note: String,
}

#[derive(Debug)]
pub enum Terminator {
    Select(
        Rc<VarDef>,
        Vec<(Box<Literal>, Rc<RefCell<Block>>)>,
        Rc<RefCell<Block>>,
    ),
    Jump(Rc<RefCell<Block>>),
    Return,
    Panic,
}

pub type BinOp = TypedASTBinOp;

#[derive(Debug)]
pub struct TypedValue {
    pub typ: usize,
    pub val: Value,
}

#[derive(Debug)]
pub enum Value {
    Call(RefPath, Vec<TypedValue>),
    ExtCall(RefPath, Vec<TypedValue>),
    Op(BinOp, Box<TypedValue>, Box<TypedValue>),
    Imm(Literal),
    Unit,
    Intrinsic(&'static str, Vec<TypedValue>),
    VarRef(Rc<VarDef>),
}

pub type Literal = TypedASTLiteral;

#[derive(Debug)]
struct FunctionBuilder<'a> {
    pub position: Option<Rc<RefCell<Block>>>,
    pub namer: UniqueName,
    pub table: SymTable<Rc<VarDef>>,
    pub func: &'a mut FuncDef,
    pub panic_block: Rc<RefCell<Block>>,
}

#[derive(Debug, Default, Clone)]
pub struct MiddleIR {
    pub ty_ctx: TypeContext,
    pub module: Vec<FuncDef>,
}

impl MiddleIR {
    fn convert_asgn(&mut self, name: &str, expr: &TypedExpr, builder: &mut FunctionBuilder) {
        let var = Rc::clone(
            builder
                .table
                .find_symbol(name)
                .unwrap_or_else(|| panic!("variable {} not defined", name)),
        );
        self.convert_expr(expr, builder, Some(var), false);
    }

    fn convert_args(
        &mut self,
        builder: &mut FunctionBuilder,
        arg: &[TypedArgument],
        param: &[usize],
    ) -> Vec<TypedValue> {
        let mut v = vec![];
        for x in arg.iter().zip(param) {
            match x.0 {
                TypedArgument::Expr(expr) => {
                    let name = builder.namer.next_name("tmp.arg");
                    let arg_var = self.create_variable_definition(name.as_str(), *x.1);
                    builder.func.tmp_def.push(Rc::clone(&arg_var));

                    self.convert_expr(expr, builder, Some(Rc::clone(&arg_var)), true);

                    v.push(TypedValue {
                        typ: *x.1,
                        val: Value::VarRef(arg_var),
                    });
                }
                TypedArgument::AtVar(name, typ) => {
                    let var_name = builder.namer.next_name("tmp.at_arg");
                    let arg_var = self.create_variable_definition(var_name.as_str(), *x.1);
                    builder.func.tmp_def.push(Rc::clone(&arg_var));

                    self.convert_expr(
                        &TypedExpr {
                            expr: Box::new(ExprEnum::Var(name.clone())),
                            typ: *typ,
                        },
                        builder,
                        Some(Rc::clone(&arg_var)),
                        true,
                    );
                    v.push(TypedValue {
                        typ: *x.1,
                        val: Value::VarRef(arg_var),
                    });
                }
            }
        }
        v
    }

    fn convert_ctor_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedCtorExpr,
    ) -> TypedValue {
        let TypedCtorExpr { typ, name, args } = x;
        let (ctor_idx, params_typ) = self
            .ty_ctx
            .get_ctor_index_and_field_type_by_name(*typ, name);
        let mut args_value = self.convert_args(
            builder,
            args,
            &params_typ.iter().map(|(ty, _)| *ty).collect::<Vec<usize>>(),
        );
        let mut v = vec![TypedValue {
            typ: SingletonType::I32,
            val: Value::Imm(Literal::Int(ctor_idx as i32)),
        }];
        v.append(&mut args_value);
        let val = Value::Intrinsic("calocom.construct", v);
        TypedValue { typ: *typ, val }
    }

    fn convert_trivial_match_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        expr: Rc<VarDef>,
        arms: &[(Pattern, TypedExpr)],
        output: Rc<VarDef>,
    ) {
        let current_bb = Rc::clone(builder.position.as_ref().unwrap());
        let current_terminator = &current_bb.as_ref().borrow().terminator;
        let next_bb = match current_terminator {
            Terminator::Jump(x) => x,
            _ => panic!("internal error: expect jump terminator now"),
        };

        let match_var = Rc::clone(&expr);
        let mut v = vec![];
        for arm in arms {
            match &arm.0 {
                Pattern::Lit(lit) => {
                    let arm_block = Rc::new(RefCell::new(Block::new(
                        &mut builder.namer,
                        vec![],
                        Terminator::Jump(Rc::clone(next_bb)),
                    )));

                    let choice = (Box::new(lit.clone()), Rc::clone(&arm_block));

                    v.push(choice);

                    let arm_position = Some(Rc::clone(&arm_block));
                    builder.position = arm_position;

                    builder.table.entry();
                    self.convert_expr(&arm.1, builder, Some(Rc::clone(&output)), false);
                    builder.table.exit();

                    builder.func.blocks.push(arm_block);
                }
                Pattern::Con(_) => panic!("can't use a non-literal match arm"),
            }
        }

        let select = Terminator::Select(match_var, v, Rc::clone(&builder.panic_block));
        current_bb.borrow_mut().terminator = select;
        let next_position = Some(Rc::clone(next_bb));
        builder.position = next_position;
    }

    fn extract_enum_tag(&mut self, builder: &mut FunctionBuilder, expr: Rc<VarDef>) -> Value {
        let name = builder.namer.next_name("tmp.enum.tag");
        let tag_var = self.create_variable_definition(name.as_str(), SingletonType::C_I32);
        builder.func.unwrapped_def.push(Rc::clone(&tag_var));

        let lhs = Some(Rc::clone(&tag_var));
        let rhs = Some(TypedValue {
            typ: tag_var.typ,
            val: Value::Intrinsic(
                "calocom.extract_tag",
                vec![TypedValue {
                    typ: expr.typ,
                    val: Value::VarRef(expr),
                }],
            ),
        });

        builder
            .position
            .as_ref()
            .unwrap()
            .borrow_mut()
            .stmts
            .push(Stmt {
                left: lhs,
                right: rhs,
                note: "extract tag of enum".to_string(),
            });

        Value::VarRef(tag_var)
    }

    fn convert_complex_match_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        expr: Rc<VarDef>,
        arms: &[(Pattern, TypedExpr)],
        output: Rc<VarDef>,
    ) {
        let current_bb = Rc::clone(builder.position.as_ref().unwrap());
        let next_bb = {
            let current_terminator = &current_bb.as_ref().borrow().terminator;
            match current_terminator {
                Terminator::Jump(x) => Rc::clone(x),
                _ => panic!("internal error: expect jump terminator now"),
            }
        };

        let match_value = self.extract_enum_tag(builder, Rc::clone(&expr));
        let match_var = match match_value {
            Value::VarRef(var) => var,
            _ => unimplemented!("match var can only be var ref"),
        };
        let mut v = vec![];
        for arm in arms.iter().enumerate() {
            match &arm.1 .0 {
                Pattern::Lit(_) => panic!("can't use a literal match arm"),
                Pattern::Con(con) => {
                    let TypedASTConstructorVar { name, inner } = con;
                    let arm_block = Rc::new(RefCell::new(Block::new(
                        &mut builder.namer,
                        vec![],
                        Terminator::Jump(Rc::clone(&next_bb)),
                    )));

                    let choice = (
                        Box::new(Literal::Int(arm.0.try_into().unwrap())),
                        Rc::clone(&arm_block),
                    );

                    v.push(choice);

                    let arm_position = Some(Rc::clone(&arm_block));
                    builder.position = arm_position;
                    builder.table.entry();

                    if let Some(inner) = inner {
                        let (ctor_idx, field_typ) = self
                            .ty_ctx
                            .get_ctor_index_and_field_type_by_name(expr.typ, name);
                        let name = builder.namer.next_name("tmp.field");
                        let field_var =
                            self.create_variable_definition(name.as_str(), field_typ[0].0);
                        builder.func.tmp_def.push(Rc::clone(&field_var));

                        let field = TypedValue {
                            typ: field_typ[0].0,
                            val: Value::Intrinsic(
                                "calocom.extract_field",
                                vec![
                                    TypedValue {
                                        typ: expr.typ,
                                        val: Value::VarRef(Rc::clone(&expr)),
                                    },
                                    TypedValue {
                                        typ: SingletonType::I32,
                                        val: Value::Imm(Literal::Int(ctor_idx as i32)),
                                    },
                                    TypedValue {
                                        typ: SingletonType::I32,
                                        val: Value::Imm(Literal::Int(0)),
                                    },
                                ],
                            ),
                        };
                        builder
                            .position
                            .as_ref()
                            .unwrap()
                            .borrow_mut()
                            .stmts
                            .push(Stmt {
                                left: Some(Rc::clone(&field_var)),
                                right: Some(field),
                                note: "extract field of enum".to_string(),
                            });

                        builder
                            .table
                            .insert_symbol(inner.clone(), Rc::clone(&field_var));
                    }
                    self.convert_expr(&arm.1 .1, builder, Some(Rc::clone(&output)), false);

                    builder.table.exit();
                    builder.func.blocks.push(arm_block);
                }
            }
        }

        let select = Terminator::Select(match_var, v, Rc::clone(&builder.panic_block));
        current_bb.borrow_mut().terminator = select;
        let next_position = Some(Rc::clone(&next_bb));
        builder.position = next_position;
    }

    fn convert_match_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedMatchExpr,
    ) -> TypedValue {
        let TypedMatchExpr { e, arms, typ } = x;

        let mut expr_typ = e.typ;

        if let Some(typ) = self.ty_ctx.get_reference_base_type(expr_typ) {
            expr_typ = typ;
        }

        let match_expr_var = self.create_variable_definition(
            builder.namer.next_name("tmp.match.expr").as_str(),
            expr_typ,
        );
        let match_output_var = self
            .create_variable_definition(builder.namer.next_name("tmp.match.output").as_str(), *typ);

        builder.func.tmp_def.push(Rc::clone(&match_expr_var));
        builder.func.tmp_def.push(Rc::clone(&match_output_var));

        self.convert_expr(e, builder, Some(Rc::clone(&match_expr_var)), false);

        if arms.is_empty() {
            if *typ != SingletonType::UNIT {
                panic!("empty match can't has return type except unit");
            }
            return TypedValue {
                typ: SingletonType::UNIT,
                val: Value::Unit,
            };
        }

        if SingletonType::is_singleton_type(expr_typ) {
            assert!(e.typ != SingletonType::OBJECT);
            assert!(e.typ != SingletonType::UNIT);
            self.convert_trivial_match_expr(
                builder,
                Rc::clone(&match_expr_var),
                arms,
                Rc::clone(&match_output_var),
            )
        } else {
            if !self.ty_ctx.is_enum_type(expr_typ) {
                panic!(
                    "can't match this type {:#?}",
                    self.ty_ctx.get_type_by_idx(e.typ)
                );
            }
            self.convert_complex_match_expr(
                builder,
                Rc::clone(&match_expr_var),
                arms,
                Rc::clone(&match_output_var),
            )
        }
        let val = Value::VarRef(match_output_var);
        TypedValue { typ: *typ, val }
    }

    fn convert_call_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedCallExpr,
    ) -> TypedValue {
        let TypedCallExpr { path, gen: _, args } = x;
        let fn_type = self
            .ty_ctx
            .find_function_type(&path.items[0])
            .unwrap()
            .clone();
        let params_typ = &fn_type.1;
        let args_value = self.convert_args(builder, args, params_typ);
        let val = Value::Call(path.clone(), args_value);
        TypedValue {
            typ: fn_type.0,
            val,
        }
    }

    fn convert_ext_call_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedExternalCallExpr,
    ) -> TypedValue {
        let TypedExternalCallExpr { path, gen: _, args } = x;
        let fn_type = &self
            .ty_ctx
            .find_external_polymorphic_function_type(&path.items)
            .unwrap()
            .clone();
        let params_typ = &fn_type.1;
        let typ = fn_type.0;
        let args_value = self.convert_args(builder, args, params_typ);
        let val = Value::ExtCall(path.clone(), args_value);

        TypedValue { typ, val }
    }

    fn convert_bracket_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedBracketBody,
    ) -> TypedValue {
        let TypedBracketBody {
            stmts,
            ret_expr,
            typ,
        } = x;
        builder.table.entry();

        let bracket_out = self.create_variable_definition("bracket.output", *typ);
        builder.func.tmp_def.push(Rc::clone(&bracket_out));

        for stmt in stmts {
            self.convert_stmt(stmt, builder)
        }

        if let Some(ret_expr) = ret_expr {
            self.convert_expr(ret_expr, builder, Some(Rc::clone(&bracket_out)), false);
        }

        builder.table.exit();
        let val = Value::VarRef(bracket_out);
        TypedValue { typ: *typ, val }
    }

    fn convert_arith_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        x: &TypedArithExpr,
    ) -> TypedValue {
        let TypedArithExpr { lhs, rhs, op, typ } = x;

        let lhs_out = self
            .create_variable_definition(builder.namer.next_name("tmp.arith.lhs").as_str(), lhs.typ);
        let rhs_out = self
            .create_variable_definition(builder.namer.next_name("tmp.arith.rhs").as_str(), rhs.typ);

        builder.func.tmp_def.push(Rc::clone(&lhs_out));
        builder.func.tmp_def.push(Rc::clone(&rhs_out));

        self.convert_expr(lhs, builder, Some(Rc::clone(&lhs_out)), false);
        self.convert_expr(rhs, builder, Some(Rc::clone(&rhs_out)), false);

        let val = Value::Op(
            op.clone(),
            Box::new(TypedValue {
                typ: lhs.typ,
                val: Value::VarRef(lhs_out),
            }),
            Box::new(TypedValue {
                typ: rhs.typ,
                val: Value::VarRef(rhs_out),
            }),
        );

        TypedValue { typ: *typ, val }
    }

    fn convert_variable_expr(&mut self, builder: &mut FunctionBuilder, x: &str) -> TypedValue {
        let var = builder
            .table
            .find_symbol(x)
            .unwrap_or_else(|| panic!("variable {} not defined", x));
        let val = Value::VarRef(var.clone());
        TypedValue { typ: var.typ, val }
    }

    fn convert_literal_expr(&mut self, x: &Literal) -> TypedValue {
        let typ = match x {
            Literal::Int(_) => SingletonType::I32,
            Literal::Str(_) => SingletonType::STR,
            Literal::Bool(_) => SingletonType::BOOL,
        };
        let val = Value::Imm(x.clone());
        TypedValue { typ, val }
    }

    fn create_value_from_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        expr: &ExprEnum,
    ) -> TypedValue {
        match expr {
            ExprEnum::MatchExpr(x) => self.convert_match_expr(builder, x),
            ExprEnum::BraExpr(x) => self.convert_bracket_expr(builder, x),
            ExprEnum::CallExpr(x) => self.convert_call_expr(builder, x),
            ExprEnum::ExtCallExpr(x) => self.convert_ext_call_expr(builder, x),
            ExprEnum::ArithExpr(x) => self.convert_arith_expr(builder, x),
            ExprEnum::CtorExpr(x) => self.convert_ctor_expr(builder, x),
            ExprEnum::Var(x) => self.convert_variable_expr(builder, x.as_str()),
            ExprEnum::Lit(x) => self.convert_literal_expr(x),
        }
    }

    fn create_dereferenced_value(
        &self,
        func: &mut FuncDef,
        namer: &mut UniqueName,
        name: &str,
        typ: usize,
    ) -> Rc<VarDef> {
        let name = namer.next_name(name);
        let base_type: Reference = self.ty_ctx.get_type_by_idx(typ).into();
        let dereferenced =
            self.create_variable_definition(name.as_str(), base_type.refer.left().unwrap());
        func.mem_ref.push(Rc::clone(&dereferenced));
        dereferenced
    }

    fn convert_expr(
        &mut self,
        expr: &TypedExpr,
        builder: &mut FunctionBuilder,
        out: Option<Rc<VarDef>>,
        get_addr: bool,
    ) {
        let mut stmt = Stmt::default();

        let TypedExpr { expr, typ } = expr;
        let val = self.create_value_from_expr(builder, expr);
        let insert_position = &mut builder.position.as_ref().unwrap().borrow_mut().stmts;

        if let Some(lhs) = out {
            let t1 = lhs.typ;
            let t2 = *typ;

            assert!(self.ty_ctx.is_compatible(t1, t2));

            if self.ty_ctx.is_type_reference_eq(t1, t2) {
                let dereferenced = self.create_dereferenced_value(
                    builder.func,
                    &mut builder.namer,
                    "ref.expr.dereferenced",
                    t2,
                );

                let dereference_stmt = Stmt {
                    left: Some(Rc::clone(&dereferenced)),
                    right: Some(TypedValue {
                        typ: dereferenced.typ,
                        val: Value::Intrinsic("calocom.dereference", vec![val]),
                    }),
                    note: "dereference left hand side".to_string(),
                };

                insert_position.push(dereference_stmt);

                stmt.left = None;
                stmt.right = Some(TypedValue {
                    typ: SingletonType::UNIT,
                    val: Value::Intrinsic(
                        "calocom.store",
                        vec![
                            TypedValue {
                                typ: lhs.typ,
                                val: Value::VarRef(lhs),
                            },
                            TypedValue {
                                typ: dereferenced.typ,
                                val: Value::VarRef(dereferenced),
                            },
                        ],
                    ),
                });

                stmt.note = "assign".to_string();
            } else if self.ty_ctx.is_type_pure_eq(t1, t2) || self.ty_ctx.is_type_opaque_eq(t1, t2) {
                stmt.left = Some(Rc::clone(&lhs));
                stmt.right = Some(val);
                stmt.note = "assign".to_string();
            } else if t1 == SingletonType::OBJECT {
                stmt.left = Some(Rc::clone(&lhs));
                stmt.right = Some(TypedValue {
                    typ: SingletonType::OBJECT,
                    val: Value::Intrinsic("calocom.erase_type", vec![val]),
                });
                stmt.note = "erase type".to_string();
            } else if t2 == SingletonType::OBJECT {
                stmt.left = Some(Rc::clone(&lhs));
                stmt.right = Some(TypedValue {
                    typ: SingletonType::OBJECT,
                    val: Value::Intrinsic("calocom.specialize_type", vec![val]),
                });
                stmt.note = "specialize type".to_string();
            } else if self.ty_ctx.is_t1_reference_of_t2(t1, t2) {
                stmt.left = None;
                stmt.right = Some(TypedValue {
                    typ: SingletonType::UNIT,
                    val: Value::Intrinsic(
                        if !get_addr {
                            "calocom.store"
                        } else {
                            "calocom.get_address"
                        },
                        vec![
                            TypedValue {
                                typ: lhs.typ,
                                val: Value::VarRef(lhs),
                            },
                            val,
                        ],
                    ),
                });
                stmt.note = "assign".to_string();
            } else if self.ty_ctx.is_t1_reference_of_t2(t2, t1) {
                let dereferenced = self.create_dereferenced_value(
                    builder.func,
                    &mut builder.namer,
                    "ref.expr.dereferenced",
                    t2,
                );

                let dereference_stmt = Stmt {
                    left: Some(Rc::clone(&dereferenced)),
                    right: Some(TypedValue {
                        typ: dereferenced.typ,
                        val: Value::Intrinsic("calocom.dereference", vec![val]),
                    }),
                    note: "dereference right hand side".to_string(),
                };

                insert_position.push(dereference_stmt);

                stmt.left = Some(Rc::clone(&lhs));
                stmt.right = Some(TypedValue {
                    typ: dereferenced.typ,
                    val: Value::VarRef(dereferenced),
                });
                stmt.note = "assign".to_string();
            } else {
                panic!("t1: {}, t2: {}", t1, t2)
            }
        } else {
            stmt.right = Some(val);
            stmt.note = "non-value statement".to_string();
        }

        assert!(stmt.right.is_some());
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
            TypedASTStmt::Expr(stmt) => self.convert_expr(stmt, builder, None, false),
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
            self.convert_expr(ret_expr, builder, out, false);
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
            with_at: _,
            var_name,
            typ,
        } in &func.param_list
        {
            let name = format!("#{}", var_name);
            let param = self.create_variable_definition(name.as_str(), *typ);

            // insert the parameter into symbol table
            sym_table.insert_symbol(var_name.to_string(), Rc::clone(&param));
            def.param_def.push(param);
        }

        // return block
        let ret_block = Rc::new(RefCell::new(Block {
            name: "exit".to_string(),
            terminator: Terminator::Return,
            stmts: vec![],
        }));

        // add an empty entry block and set the insert point
        let entry_block = Rc::new(RefCell::new(Block {
            name: "entry".to_string(),
            terminator: Terminator::Jump(Rc::clone(&ret_block)),
            stmts: vec![],
        }));

        let panic_block = Rc::new(RefCell::new(Block {
            name: "panic".to_string(),
            terminator: Terminator::Panic,
            stmts: vec![],
        }));

        let position = Rc::clone(&entry_block);

        def.blocks.push(entry_block);
        def.blocks.push(ret_block);
        def.blocks.push(Rc::clone(&panic_block));

        let mut fn_builder = FunctionBuilder {
            func: &mut def,
            position: Some(position),
            namer: UniqueName::new(),
            table: sym_table,
            panic_block,
        };

        // convert the function body
        self.convert_bracket_body(&func.body, &mut fn_builder, Some(Rc::clone(&ret)));

        // exit the symbol table scope
        fn_builder.table.exit();
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

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedASTLiteral::Int(i) => write!(f, "{}", i),
            TypedASTLiteral::Str(s) => write!(f, "{:?}", s),
            TypedASTLiteral::Bool(b) => write!(f, "{}", b),
        }
    }
}

impl Display for RefPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.items.join("."))
    }
}

impl Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Terminator::Select(val, targets, other) => {
                write!(f, "select {} [", val)?;
                for (idx, target) in targets.iter().enumerate() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} => {}", target.0, target.1.as_ref().borrow().name)?;
                }
                write!(f, ", _ => {}]", other.as_ref().borrow().name)
            }
            Terminator::Jump(target) => write!(f, "jump {}", target.as_ref().borrow().name),
            Terminator::Return => write!(f, "ret"),
            Terminator::Panic => write!(f, "panic"),
        }
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:", self.name)?;
        for stmt in &self.stmts {
            writeln!(f, "    {}", stmt)?;
        }
        write!(f, "    {}", self.terminator)
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedASTBinOp::Plus => write!(f, "add"),
            TypedASTBinOp::Sub => write!(f, "sub"),
            TypedASTBinOp::Mult => write!(f, "mul"),
            TypedASTBinOp::Div => write!(f, "div"),
            TypedASTBinOp::Mod => write!(f, "mod"),
        }
    }
}

impl Display for VarDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Display for TypedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} : type[{}])", self.val, self.typ)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let print_vec_of_values = |f: &mut std::fmt::Formatter<'_>, values: &Vec<TypedValue>| {
            for (idx, val) in values.iter().enumerate() {
                if idx != 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}", val)?;
            }
            write!(f, "")
        };
        match self {
            Value::ExtCall(path, args) => {
                write!(f, "extern {} ", path)?;
                print_vec_of_values(f, args)
            }
            Value::Call(path, args) => {
                write!(f, "{} ", path)?;
                print_vec_of_values(f, args)
            }
            Value::Op(op, l, r) => write!(f, "{} {} {}", op, l, r),
            Value::Imm(imm) => write!(f, "{}", imm),
            Value::Unit => write!(f, "unit"),
            Value::Intrinsic(name, args) => {
                write!(f, "@{} ", name)?;
                print_vec_of_values(f, args)
            }
            Value::VarRef(var) => write!(f, "{}", var),
        }
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(left) = &self.left {
            write!(f, "{: <24} = {};", left.name, self.right.as_ref().unwrap())
        } else {
            write!(f, "{: <24} = {};", "()", self.right.as_ref().unwrap())
        }
    }
}

impl Display for MiddleIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}\n", self.ty_ctx)?;
        let (_, type_name_map) = self.ty_ctx.get_display_name_map();
        for func in self.module.iter() {
            let FuncDef {
                name,
                param_def,
                var_def,
                tmp_def,
                mem_ref,
                ret_def,
                blocks,
                unwrapped_def,
            } = func;

            writeln!(f, "fn {} {{", name)?;
            let mut print_var = |var: &Rc<VarDef>| {
                writeln!(
                    f,
                    "    {}: {}",
                    var.name,
                    type_name_map.get(&var.typ).unwrap(),
                )
            };

            print_var(ret_def.as_ref().unwrap())?;
            param_def
                .iter()
                .map(&mut print_var)
                .collect::<Result<Vec<_>, _>>()?;
            var_def
                .iter()
                .map(&mut print_var)
                .collect::<Result<Vec<_>, _>>()?;
            tmp_def
                .iter()
                .map(&mut print_var)
                .collect::<Result<Vec<_>, _>>()?;
            mem_ref
                .iter()
                .map(&mut print_var)
                .collect::<Result<Vec<_>, _>>()?;
            unwrapped_def
                .iter()
                .map(&mut print_var)
                .collect::<Result<Vec<_>, _>>()?;

            writeln!(f)?;
            for block in blocks {
                writeln!(f, "{}", block.as_ref().borrow())?;
            }

            writeln!(f, "}}\n")?;
        }
        writeln!(f)
    }
}

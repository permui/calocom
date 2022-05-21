use slotmap::{new_key_type, SlotMap};
use std::fmt::Display;
use std::fmt::Write;
use std::{panic, vec};

use super::typed_ast::*;
use crate::common::dump::*;
use crate::common::name_context::NameContext;
use crate::common::type_context::*;
use crate::common::unique_name::*;

type Literal = TypedASTLiteral;
type BinOp = TypedASTBinOp;
type UnaryOp = TypedASTUnaryOp;

new_key_type! {
    pub struct VarDefRef;
    pub struct BlockRef;
}

#[derive(Debug, Default, Clone)]
pub struct FuncDef {
    pub name: String,
    pub blocks: SlotMap<BlockRef, Block>,
    pub variables: SlotMap<VarDefRef, VarDef>,

    pub params: Vec<VarDefRef>,
    pub locals: Vec<VarDefRef>, // represents a local stack slot containing a pointer to a object
    pub temporaries: Vec<VarDefRef>, // be the same as var_def but it's not named by users
    pub obj_reference: Vec<VarDefRef>, // only represents a local stack slot containing a ptr to a ptr to a object
    pub unwrapped: Vec<VarDefRef>,     // represents a local slot for unwrapped value
    pub return_value: Option<VarDefRef>, // represents the reference to the stack slot where the return value locates

    pub entry_block: BlockRef,
    pub return_block: BlockRef,
    pub panic_block: BlockRef,
}

enum VariableKind {
    Parameter,
    LocalVariable,
    TemporaryVariable,
    RawVariable,
    ReturnVariable,
    ObjectReference,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct VarDef {
    pub name: String,
    pub typ: TypeRef,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub name: String,
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

impl Block {
    fn new(
        namer: &mut UniqueName,
        name: Option<&str>,
        stmts: Vec<Stmt>,
        terminator: Terminator,
    ) -> Self {
        Block {
            name: namer.next_name(name.unwrap_or("block")),
            stmts,
            terminator,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Stmt {
    pub left: Option<VarDefRef>,
    pub right: Option<Value>,
    pub note: &'static str,
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Select(Operand, Vec<(Literal, BlockRef)>, BlockRef),
    Branch(Operand, BlockRef, BlockRef),
    Jump(BlockRef),
    Return,
    Panic,
}

#[derive(Debug, Clone)]
pub struct Value {
    pub typ: TypeRef,
    pub val: ValueEnum,
}

#[derive(Debug, Clone)]
pub struct Operand {
    pub typ: TypeRef,
    pub val: Box<OperandEnum>,
}

#[derive(Debug, Clone)]
pub enum OperandEnum {
    Imm(Literal),
    Var(VarDefRef),
}

#[derive(Debug, Clone)]
pub enum ValueEnum {
    Call(Vec<String>, Vec<Operand>),
    ExtCall(Vec<String>, Vec<Operand>),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
    MakeTuple(Vec<Operand>),
    Construct(usize, Vec<Operand>),
    Intrinsic(&'static str, Vec<Operand>),
    Index(Operand, Operand),
    Operand(Operand),
}

#[derive(Debug)]
struct FunctionBuilder<'a> {
    pub position: Option<BlockRef>,
    pub namer: UniqueName,
    pub var_ctx: NameContext<VarDefRef>,
    pub name_ctx: &'a NameContext<TypeRef>,
    pub ty_ctx: &'a TypeContext,
    pub func: &'a mut FuncDef,
    pub continue_blocks: Vec<BlockRef>,
    pub break_blocks: Vec<BlockRef>,
}

#[derive(Debug, Default, Clone)]
pub struct MiddleIR {
    pub name_ctx: NameContext<TypeRef>,
    pub ty_ctx: TypeContext,
    pub module: Vec<FuncDef>,
}

impl FuncDef {
    fn create_variable_definition(
        &mut self,
        name: &str,
        typ: TypeRef,
        kind: VariableKind,
    ) -> VarDefRef {
        let name = name.to_string();
        let var_ref = self.variables.insert(VarDef { name, typ });
        if let VariableKind::ReturnVariable = kind {
            self.return_value
                .and_then(|_| -> Option<()> { panic!("a return value has been inserted") });
            self.return_value = Some(var_ref);
        } else {
            match kind {
                VariableKind::Parameter => &mut self.params,
                VariableKind::LocalVariable => &mut self.locals,
                VariableKind::TemporaryVariable => &mut self.temporaries,
                VariableKind::ObjectReference => &mut self.obj_reference,
                VariableKind::RawVariable => &mut self.unwrapped,
                _ => unreachable!(),
            }
            .push(var_ref);
        }
        var_ref
    }

    fn initialize_blocks(&mut self) {
        self.entry_block = self.blocks.insert(Block {
            name: "entry".to_string(),
            terminator: Terminator::Panic,
            stmts: vec![],
        });

        self.return_block = self.blocks.insert(Block {
            name: "exit".to_string(),
            terminator: Terminator::Return,
            stmts: vec![],
        });

        self.blocks.get_mut(self.entry_block).unwrap().terminator =
            Terminator::Jump(self.return_block);

        self.panic_block = self.blocks.insert(Block {
            name: "panic".to_string(),
            terminator: Terminator::Panic,
            stmts: vec![],
        });
    }

    fn get_var_type(&self, var_def: VarDefRef) -> TypeRef {
        self.variables.get(var_def).unwrap().typ
    }

    fn get_var_def(&self, var_def: VarDefRef) -> &VarDef {
        self.variables.get(var_def).unwrap()
    }

    fn get_block(&self, block_ref: BlockRef) -> &Block {
        self.blocks.get(block_ref).unwrap()
    }

    fn create_block(
        &mut self,
        namer: &mut UniqueName,
        name: Option<&str>,
        term: Option<Terminator>,
    ) -> BlockRef {
        self.blocks.insert(Block::new(
            namer,
            name,
            vec![],
            term.unwrap_or(Terminator::Panic),
        ))
    }
}

impl<'a> FunctionBuilder<'a> {
    fn create(
        func: &'a mut FuncDef,
        entry: BlockRef,
        var_ctx: NameContext<VarDefRef>,
        name_ctx: &'a NameContext<TypeRef>,
        ty_ctx: &'a TypeContext,
    ) -> Self {
        FunctionBuilder {
            func,
            position: Some(entry),
            namer: UniqueName::new(),
            var_ctx,
            name_ctx,
            ty_ctx,
            continue_blocks: vec![],
            break_blocks: vec![],
        }
    }

    fn build_function_body(&mut self, body: &TypedBracketBody, ret: VarDefRef) {
        self.build_bracket(body, Some(ret));
    }

    fn build_stmt(&mut self, stmt: &TypedASTStmt) {
        use TypedASTStmt::*;
        match stmt {
            Let(x) => self.build_let(x),
            While(x) => self.build_while(x),
            For(x) => self.build_for(x),
            Asgn(x) => self.build_asgn(x),
            Expr(x) => self.build_expr_and_assign_to(x, None),
            Return | Break | Continue => self.build_return_break_continue(stmt),
        }
    }

    fn build_return_break_continue(&mut self, stmt: &TypedASTStmt) {
        match stmt {
            TypedASTStmt::Return => {
                self.change_terminator_at_position(Terminator::Jump(self.func.return_block));
                let next_block = self.create_block(None, None);
                self.position = Some(next_block);
            }
            TypedASTStmt::Break => {
                let Some(closest) = self.break_blocks.last() else {panic!("break outside loop statement")};
                self.change_terminator_at_position(Terminator::Jump(*closest));
                let next_block = self.create_block(None, None);
                self.position = Some(next_block);
            }
            TypedASTStmt::Continue => {
                let Some(closest) = self.continue_blocks.last() else {panic!("continue outside loop statement")};
                self.change_terminator_at_position(Terminator::Jump(*closest));
                let next_block = self.create_block(None, None);
                self.position = Some(next_block);
            }
            _ => unreachable!(),
        }
    }

    fn build_let(&mut self, stmt: &TypedLetStmt) {
        let TypedLetStmt {
            var_name,
            var_type,
            expr,
        } = stmt;

        let name = self.namer.next_name(var_name);
        let new_var = self.func.create_variable_definition(
            name.as_str(),
            *var_type,
            VariableKind::LocalVariable,
        );

        self.build_expr_and_assign_to(expr, Some(new_var));
        let _: Option<()> = self
            .var_ctx
            .insert_symbol(var_name.clone(), new_var)
            .and(None);
    }

    fn build_bracket(&mut self, body: &TypedBracketBody, out: Option<VarDefRef>) {
        self.var_ctx.entry_scope();
        for stmt in &body.stmts {
            self.build_stmt(stmt);
        }
        if let Some(ret_expr) = &body.ret_expr {
            self.build_expr_and_assign_to(ret_expr, out);
        } else {
            self.build_expr_and_assign_to(
                &TypedExpr {
                    expr: Box::new(ExprEnum::Lit(Literal::Unit)),
                    typ: self.ty_ctx.singleton_type(Primitive::Unit),
                },
                out,
            );
        }
        self.var_ctx.exit_scope();
    }

    fn build_while(&mut self, stmt: &TypedWhileStmt) {
        let TypedWhileStmt { condition, body } = stmt;
        // last block          <-- position (before build while)
        //
        // cond block   <======+
        // ...                 |
        // cond end block -+   |
        //                 |   |
        // body block   <--+   |
        // ...             |   |
        // body end block =+===+
        //                 |
        // end block    <--+   <-- position

        let cond_block = self.create_block(Some("while.cond.start"), None);
        let end_block = self.create_block(Some("while.end"), None);
        let body_block = self.create_block(Some("while.body.start"), None);

        self.continue_blocks.push(cond_block);
        self.break_blocks.push(end_block);

        // record the terminator
        // update its terminator to jump to the condition block
        self.position.unwrap();
        let old_terminator_of_last_block =
            self.change_terminator_at_position(Terminator::Jump(cond_block));

        // start codegen of conditional part
        self.position = Some(cond_block);
        let cond_operand = self.build_expr_as_operand(condition);
        assert!(self.ty_ctx.is_boolean_testable_type(cond_operand.typ));

        // update the terminator of cond end block
        // to branch to body block or end block
        self.position.unwrap();
        self.change_terminator_at_position(Terminator::Branch(cond_operand, body_block, end_block));

        // start codegen of body part
        // change its terminator to loop back to the cond block
        self.var_ctx.entry_scope();
        self.position = Some(body_block);
        self.build_bracket(body, None);
        self.change_terminator_at_position(Terminator::Jump(cond_block));
        self.var_ctx.exit_scope();

        // move to end block
        // change its terminator to the old terminator of last block
        self.position = Some(end_block);
        self.change_terminator_at_position(old_terminator_of_last_block);

        self.continue_blocks.pop();
        self.break_blocks.pop();
    }

    fn build_for(&mut self, stmt: &TypedForStmt) {
        let TypedForStmt {
            var_name,
            range_l,
            range_r,
            body,
        } = stmt;

        // last block          <-- position (before build for)
        //
        // check block  <======+
        //                 |   |
        //                 |   |
        // body block   <--+   |
        // ...             |   |
        // body end block =|===+
        //                 |
        // end block    <--+   <-- position

        let check_block = self.create_block(Some("for.check.start"), None);
        let end_block = self.create_block(Some("for.end"), None);
        let body_block = self.create_block(Some("for.body.start"), None);

        self.position.unwrap();
        let old_terminator_of_last_block =
            self.change_terminator_at_position(Terminator::Jump(check_block));

        self.continue_blocks.push(check_block);
        self.break_blocks.push(end_block);

        self.var_ctx.entry_scope();

        // this is the induction variable
        let name = self.namer.next_name(var_name);
        let ind_var = self.func.create_variable_definition(
            name.as_str(),
            range_l.typ,
            VariableKind::LocalVariable,
        );

        // we assign the initial value to the induction variable
        self.build_expr_and_assign_to(range_l, Some(ind_var));

        // we calculate the termination value of the for range
        let term_value_name = self.namer.next_name("for.range.terminate");
        let term_value = self.func.create_variable_definition(
            term_value_name.as_str(),
            range_r.typ,
            VariableKind::TemporaryVariable,
        );

        // allow to find the reference to induction variable
        let _: Option<()> = self
            .var_ctx
            .insert_symbol(var_name.clone(), ind_var)
            .and(None);

        // move to check block;
        self.position = Some(check_block);

        // this is the test result of equality of induction variable and termination value
        let cond_check_name = self.namer.next_name("for.cond.check");
        let cond_check_var = self.func.create_variable_definition(
            cond_check_name.as_str(),
            self.ty_ctx.singleton_type(Primitive::Bool),
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(cond_check_var),
            right: Some(Value {
                typ: self.ty_ctx.singleton_type(Primitive::Bool),
                val: ValueEnum::BinaryOp(
                    BinOp::Eq,
                    self.build_operand_from_var_def(ind_var),
                    self.build_operand_from_var_def(term_value),
                ),
            }),
            note: "for termination check",
        });

        self.change_terminator_at_position(Terminator::Branch(
            self.build_operand_from_var_def(cond_check_var),
            body_block,
            end_block,
        ));

        self.position = Some(body_block);
        self.build_bracket(body, None);
        self.change_terminator_at_position(Terminator::Jump(check_block));

        self.insert_stmt_at_position(Stmt {
            left: Some(ind_var),
            right: Some(Value {
                typ: self.ty_ctx.singleton_type(Primitive::Bool),
                val: ValueEnum::BinaryOp(
                    BinOp::Plus,
                    self.build_operand_from_literal(Literal::Int(1)),
                    self.build_operand_from_var_def(ind_var),
                ),
            }),
            note: "for induction variable increment",
        });

        self.var_ctx.exit_scope();

        self.position = Some(end_block);
        self.change_terminator_at_position(old_terminator_of_last_block);

        self.continue_blocks.pop();
        self.break_blocks.pop();
    }

    fn build_asgn(&mut self, stmt: &TypedAsgnStmt) {
        let TypedAsgnStmt { lhs, rhs } = stmt;
        let place = self.build_assignee_expr_as_var_def(lhs);
        self.build_expr_and_assign_to(rhs, Some(place));
    }

    fn build_expr_as_operand(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr {
            expr: expr_enum, ..
        } = expr;

        let expr_enum = expr_enum.as_ref();

        match expr_enum {
            ExprEnum::Closure { .. } => self.build_closure_expr(expr),
            ExprEnum::Match { .. } => self.build_match_expr(expr),
            ExprEnum::If { .. } => self.build_if_expr(expr),
            ExprEnum::BinOp { .. } => self.build_binary_operation_expr(expr),
            ExprEnum::UnaryOp { .. } => self.build_unary_operation_expr(expr),
            ExprEnum::Subscript { .. } => self.build_subscript_expr(expr),
            ExprEnum::ClosureCall { .. } => self.build_closure_call_expr(expr),
            ExprEnum::CtorCall { .. } => self.build_constructor_expr(expr),
            ExprEnum::Call { .. } => self.build_call_expr(expr),
            ExprEnum::Tuple { .. } => self.build_tuple_expr(expr),
            ExprEnum::Lit(..) => self.build_literal_expr(expr),
            ExprEnum::Path { .. } => self.build_path_expr(expr),
            ExprEnum::Bracket { .. } => self.build_bracket_expr(expr),
        }
    }

    fn build_expr_and_assign_to(&mut self, expr: &TypedExpr, out: Option<VarDefRef>) {
        let mut operand = self.build_expr_as_operand(expr);

        if let Some(out) = out {
            let out_ty = self.get_var_type(out);
            operand = self.build_type_conversion_if_need(operand, out_ty);
        }

        self.insert_stmt_at_position(Stmt {
            left: out,
            right: Some(self.build_value_from_operand(operand)),
            note: "build expression and assign to",
        })
    }

    fn build_type_conversion_if_need(&mut self, source: Operand, target_type: TypeRef) -> Operand {
        let source_type = source.typ;

        if self.ty_ctx.is_type_eq(source_type, target_type) {
            return source;
        }
        assert!(self.ty_ctx.is_type_compatible(source_type, target_type));

        let name = self.namer.next_name("conversion");
        let result = self.func.create_variable_definition(
            name.as_str(),
            target_type,
            VariableKind::TemporaryVariable,
        );
        self.insert_stmt_at_position(Stmt {
            left: Some(result),
            right: Some(Value {
                typ: target_type,
                val: ValueEnum::Intrinsic("convert", vec![source]),
            }),
            note: "convert",
        });

        self.build_operand_from_var_def(result)
    }

    fn build_assignee_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        self.check_assignee(expr);
        match expr.expr.as_ref() {
            ExprEnum::Subscript { .. } => self.build_subscript_expr_as_var_def(expr),
            ExprEnum::ClosureCall { .. } => todo!(),
            ExprEnum::Call { .. } => self.build_call_expr_as_var_def(expr),
            ExprEnum::Path { .. } => self.build_path_expr_as_var_def(expr),
            _ => unreachable!("check assignee missed"),
        }
    }

    fn check_assignee(&mut self, expr: &TypedExpr) {
        match expr.expr.as_ref() {
            ExprEnum::Closure { .. } => panic!("closure isn't assignable"),
            ExprEnum::Match { .. } => panic!("match expression isn't assignable"),
            ExprEnum::If { .. } => panic!("if expression isn't assignable"),
            ExprEnum::BinOp { .. } => {
                panic!("binary operation expression isn't assignable")
            }
            ExprEnum::UnaryOp { .. } => panic!("unary operation expression isn't assignable"),
            ExprEnum::CtorCall { .. } => panic!("constructor expression isn't assignable"),
            ExprEnum::Tuple { .. } => panic!("tuple expression isn't assignable"),
            ExprEnum::Lit(_) => panic!("literal isn't assignable"),
            ExprEnum::Bracket { .. } => panic!("block expression isn't assignable"),
            _ => (),
        }
    }

    fn build_closure_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_match_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_if_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::If { condition, then, or } = expr.as_ref() else { unreachable!() };
        let typ = *typ;
        let has_else = or.is_some();

        // last block          <-- position (before build if)
        //
        // cond block ----------+
        //                      |
        // then block   <-------+
        // ...                  |
        // then end block =+    |
        //                 |    |
        // else block   <--+----+
        // ...             |
        // else end block  |
        //                 |
        // end block    <==+   <-- position

        let cond_block = self.create_block(Some("if.cond"), None);
        let end_block = self.create_block(Some("if.end"), None);
        let then_block = self.create_block(Some("if.then"), None);
        let else_block = if has_else {
            Some(self.create_block(Some("if.else"), None))
        } else {
            None
        };

        let if_out_name = self.namer.next_name("if.result");
        let if_out = self.func.create_variable_definition(
            if_out_name.as_str(),
            typ,
            VariableKind::TemporaryVariable,
        );

        self.position.unwrap();
        let old_terminator_of_last_block =
            self.change_terminator_at_position(Terminator::Jump(cond_block));

        self.position = Some(cond_block);
        let cond_check_name = self.namer.next_name("if.cond.check");
        let cond_check_var = self.func.create_variable_definition(
            cond_check_name.as_str(),
            self.ty_ctx.singleton_type(Primitive::Bool),
            VariableKind::TemporaryVariable,
        );

        self.build_expr_and_assign_to(condition, Some(cond_check_var));
        self.change_terminator_at_position(Terminator::Branch(
            self.build_operand_from_var_def(cond_check_var),
            then_block,
            else_block.unwrap_or(end_block),
        ));

        self.position = Some(then_block);
        self.build_expr_and_assign_to(then, Some(if_out));
        self.change_terminator_at_position(Terminator::Jump(end_block));

        if let Some(else_block) = else_block {
            self.position = Some(else_block);
            self.build_expr_and_assign_to(or.as_ref().unwrap(), Some(if_out));
            self.change_terminator_at_position(Terminator::Jump(end_block));
        } else {
            self.build_unit_and_assign_to(if_out);
        }

        self.position = Some(end_block);
        self.change_terminator_at_position(old_terminator_of_last_block);

        self.build_operand_from_var_def(if_out)
    }

    fn build_binary_operation_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::BinOp { lhs, rhs, op } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let left_operand = self.build_expr_as_operand(lhs);
        let right_operand = self.build_expr_as_operand(rhs);

        let name = self.namer.next_name("binary.op.result");
        let result = self.func.create_variable_definition(
            name.as_str(),
            typ,
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(result),
            right: Some(Value {
                typ,
                val: ValueEnum::BinaryOp(*op, left_operand, right_operand),
            }),
            note: "binary operation",
        });

        self.build_operand_from_var_def(result)
    }

    fn build_unary_operation_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::UnaryOp { expr, op } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let operand = self.build_expr_as_operand(expr);

        let name = self.namer.next_name("unary.op.result");
        let result = self.func.create_variable_definition(
            name.as_str(),
            typ,
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(result),
            right: Some(Value {
                typ,
                val: ValueEnum::UnaryOp(*op, operand),
            }),
            note: "binary operation",
        });

        self.build_operand_from_var_def(result)
    }

    fn build_subscript_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Subscript { arr, index } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let arr = self.build_expr_as_operand(arr);
        let index = self.build_expr_as_operand(index);
        let name = self.namer.next_name("elem");
        let result =
            self.func
                .create_variable_definition(name.as_str(), typ, VariableKind::ObjectReference);

        self.insert_stmt_at_position(Stmt {
            left: Some(result),
            right: Some(Value {
                typ,
                val: ValueEnum::Index(arr, index),
            }),
            note: "array subscription",
        });

        result
    }

    fn build_subscript_expr(&mut self, expr: &TypedExpr) -> Operand {
        let result = self.build_subscript_expr_as_var_def(expr);
        self.build_operand_from_var_def(result)
    }

    fn build_closure_call_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_constructor_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::CtorCall { name, args  } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let (ctor_index, params_type) = self
            .ty_ctx
            .get_ctor_index_and_field_type_ref_by_name(typ, name);
        let args_value = self.build_arguments(args, &params_type);

        let constructed_name = self.namer.next_name("enum.constructed");
        let construction_result = self.func.create_variable_definition(
            constructed_name.as_str(),
            typ,
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(construction_result),
            right: Some(Value {
                typ,
                val: ValueEnum::Construct(ctor_index, args_value),
            }),
            note: "construct an enum here",
        });

        self.build_operand_from_var_def(construction_result)
    }

    fn build_call_expr(&mut self, expr: &TypedExpr) -> Operand {
        let result = self.build_call_expr_as_var_def(expr);
        self.build_operand_from_var_def(result)
    }

    fn build_call_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        let TypedExpr { expr, .. } = expr;
        let ExprEnum::Call { path, args, ..  } = expr.as_ref() else { unreachable!() };

        let fn_type = self
            .name_ctx
            .find_symbol(path)
            .unwrap_or_else(|| panic!("can't found function {}", path.join(".")));

        let Type::Callable { kind , ret_type, parameters } = self.ty_ctx.get_type_by_ref(fn_type) else {
            unreachable!();
        };

        if kind != CallKind::Function {
            panic!("internal error");
        }

        let args_operands = self.build_arguments(args, &parameters);

        let name = self.namer.next_name("call.result");
        let call_result = self.func.create_variable_definition(
            name.as_str(),
            ret_type,
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(call_result),
            right: Some(Value {
                typ: ret_type,
                val: ValueEnum::Call(path.to_vec(), args_operands),
            }),
            note: "make a call here",
        });

        call_result
    }

    fn build_arguments(&mut self, args: &[TypedArgument], types: &[TypeRef]) -> Vec<Operand> {
        let mut vec = vec![];
        for (arg, &type_ref) in args.iter().zip(types.iter()) {
            match arg {
                TypedArgument::Expr(expr) => {
                    let name = self.namer.next_name("arg");
                    let arg_var = self.func.create_variable_definition(
                        name.as_str(),
                        type_ref,
                        VariableKind::TemporaryVariable,
                    );

                    self.build_expr_and_assign_to(expr, Some(arg_var));
                    vec.push(self.build_operand_from_var_def(arg_var));
                }
                TypedArgument::AtVar(name, typ) => {
                    let arg_name = self.namer.next_name("at_arg");
                    let arg_var = self.func.create_variable_definition(
                        arg_name.as_str(),
                        type_ref,
                        VariableKind::TemporaryVariable,
                    );

                    self.build_expr_and_assign_to(
                        &TypedExpr {
                            expr: Box::new(ExprEnum::Path {
                                path: [name.clone()].to_vec(),
                                is_free_variable: false,
                            }),
                            typ: *typ,
                        },
                        Some(arg_var),
                    );
                    vec.push(self.build_operand_from_var_def(arg_var));
                }
            }
        }
        vec
    }

    fn build_tuple_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Tuple { elements } = expr.as_ref() else { unreachable!() };
        let mut fields = vec![];
        let typ = *typ;

        for element in elements.iter() {
            let name = self.namer.next_name("make.tuple.field");
            let field = self.func.create_variable_definition(
                name.as_str(),
                element.typ,
                VariableKind::TemporaryVariable,
            );
            fields.push(self.build_operand_from_var_def(field));
            self.build_expr_and_assign_to(element, Some(field));
        }

        let name = self.namer.next_name("make.tuple");
        let tuple = self.func.create_variable_definition(
            name.as_str(),
            typ,
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(tuple),
            right: Some(Value {
                typ,
                val: ValueEnum::MakeTuple(fields),
            }),
            note: "make a tuple here",
        });

        self.build_operand_from_var_def(tuple)
    }

    fn build_literal_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Lit(lit) = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        Operand {
            typ,
            val: Box::new(OperandEnum::Imm(lit.clone())),
        }
    }

    fn build_path_expr(&mut self, expr: &TypedExpr) -> Operand {
        let result = self.build_path_expr_as_var_def(expr);
        self.build_operand_from_var_def(result)
    }

    fn build_path_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        // assure here is only variable path, not function path or ctor path
        let TypedExpr { expr, .. } = expr;
        let ExprEnum::Path { path, .. } = expr.as_ref() else { unreachable!() };
        let var = self
            .var_ctx
            .find_symbol(path)
            .unwrap_or_else(|| panic!("variable {} not defined", path.join(".")));

        var
    }

    fn build_bracket_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Bracket { stmts, ret_expr } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let name = self.namer.next_name("bracket.out");
        let output_var = self.func.create_variable_definition(
            name.as_str(),
            typ,
            VariableKind::TemporaryVariable,
        );

        self.var_ctx.entry_scope();
        for stmt in stmts.iter() {
            self.build_stmt(stmt);
        }
        if let Some(ret_expr) = ret_expr {
            self.build_expr_and_assign_to(ret_expr, Some(output_var));
        } else {
            self.build_unit_and_assign_to(output_var);
        }
        self.var_ctx.exit_scope();
        self.build_operand_from_var_def(output_var)
    }

    fn build_value_from_operand(&self, operand: Operand) -> Value {
        Value {
            typ: operand.typ,
            val: ValueEnum::Operand(operand),
        }
    }

    fn build_operand_from_var_def(&self, var_def: VarDefRef) -> Operand {
        Operand {
            typ: self.get_var_type(var_def),
            val: Box::new(OperandEnum::Var(var_def)),
        }
    }

    fn build_operand_from_var_def_with_type(
        &mut self,
        typ: TypeRef,
        var_def: VarDefRef,
    ) -> Operand {
        self.build_type_conversion_if_need(self.build_operand_from_var_def(var_def), typ)
    }

    fn build_operand_from_literal(&self, literal: Literal) -> Operand {
        let typ = match literal {
            Literal::Float(_) => self.ty_ctx.singleton_type(Primitive::Float64),
            Literal::Int(_) => self.ty_ctx.singleton_type(Primitive::Int32),
            Literal::Str(_) => self.ty_ctx.singleton_type(Primitive::Str),
            Literal::Bool(_) => self.ty_ctx.singleton_type(Primitive::Bool),
            Literal::Unit => self.ty_ctx.singleton_type(Primitive::Unit),
        };
        Operand {
            typ,
            val: Box::new(OperandEnum::Imm(literal)),
        }
    }

    fn build_value_from_var_def(&self, var_def: VarDefRef) -> Value {
        let operand = self.build_operand_from_var_def(var_def);
        self.build_value_from_operand(operand)
    }

    fn build_unit_and_assign_to(&mut self, output_var: VarDefRef) {
        self.build_expr_and_assign_to(
            &TypedExpr {
                expr: Box::new(ExprEnum::Lit(Literal::Unit)),
                typ: self.ty_ctx.singleton_type(Primitive::Unit),
            },
            Some(output_var),
        );
    }

    fn get_var_def(&self, var_def: VarDefRef) -> &VarDef {
        self.func.get_var_def(var_def)
    }

    fn get_var_type(&self, var_def: VarDefRef) -> TypeRef {
        self.func.get_var_type(var_def)
    }

    fn get_block(&self, block_ref: BlockRef) -> &Block {
        self.func.get_block(block_ref)
    }

    fn create_block(&mut self, name: Option<&str>, term: Option<Terminator>) -> BlockRef {
        self.func.create_block(&mut self.namer, name, term)
    }

    fn insert_stmt_at_position(&mut self, stmt: Stmt) {
        let block_ref = self.position.expect("expect a insert position");
        let block = self.func.blocks.get_mut(block_ref).unwrap();
        block.stmts.push(stmt);
    }

    fn change_terminator_at_position(&mut self, term: Terminator) -> Terminator {
        let block_ref = self.position.expect("expect a insert position");
        let block = self.func.blocks.get_mut(block_ref).unwrap();
        let old = block.terminator.clone();
        block.terminator = term;
        old
    }
}

impl From<TypedAST> for MiddleIR {
    fn from(tast: TypedAST) -> Self {
        MiddleIR::create_from_ast(tast)
    }
}

impl MiddleIR {
    pub fn create_from_ast(ty_ast: TypedAST) -> Self {
        let TypedAST {
            name_ctx,
            ty_ctx,
            module,
            delimiter: _,
        } = ty_ast;

        let name_ctx = NameContext::inherit_environment(name_ctx);
        let mut mir = MiddleIR {
            name_ctx,
            ty_ctx,
            ..Default::default()
        };

        mir.convert_ast(&module);

        mir
    }

    fn convert_ast(&mut self, fn_def: &Vec<TypedFuncDef>) {
        for func in fn_def {
            let new_def = self.convert_fn_definition(func);
            self.module.push(new_def);
        }
    }

    fn convert_fn_definition(&mut self, func: &TypedFuncDef) -> FuncDef {
        let mut def = FuncDef {
            name: func.name.clone(),
            ..Default::default()
        };

        // setup the symbol table
        let mut var_ctx: NameContext<VarDefRef> = Default::default();

        // create the return value variable
        let ret_var =
            def.create_variable_definition("#ret.var", func.ret_type, VariableKind::ReturnVariable);

        // insert the return value variable
        var_ctx.entry_scope();
        var_ctx
            .insert_symbol("ret.var".to_string(), ret_var)
            .unwrap_or_default();

        for TypedBind {
            with_at: _,
            var_name,
            typ,
        } in &func.params
        {
            let name = format!("#{var_name}");
            let param =
                def.create_variable_definition(name.as_str(), *typ, VariableKind::Parameter);

            var_ctx
                .insert_symbol(var_name.to_string(), param)
                .unwrap_or_default();
        }

        def.initialize_blocks();
        let entry_block = def.entry_block;
        let mut fn_builder =
            FunctionBuilder::create(&mut def, entry_block, var_ctx, &self.name_ctx, &self.ty_ctx);

        // convert the function body
        fn_builder.build_function_body(&func.body, ret_var);

        // exit the symbol table scope (1: bracket scope, 2: parameter scope)
        fn_builder.var_ctx.exit_scope();
        def
    }

    fn get_type(&self, typ: TypeRef) -> Type {
        self.ty_ctx.get_type_by_ref(typ)
    }
}

impl Display for MiddleIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.dump_string())
    }
}

impl Dump for Literal {
    fn dump_string(&self) -> String {
        match self {
            Literal::Int(i) => format!("{i}"),
            Literal::Str(s) => format!("{s:?}"),
            Literal::Bool(b) => format!("{b}"),
            Literal::Float(d) => format!("{d}"),
            Literal::Unit => "()".to_string(),
        }
    }
}

impl Dump for (&TypeContext, TypeRef) {
    fn dump_string(&self) -> String {
        let (ty_ctx, typ) = self;
        ty_ctx.get_type_ref_string(*typ)
    }
}

impl Dump for (&FuncDef, BlockRef) {
    fn dump_string(&self) -> String {
        let (func, block) = self;
        let block = func.get_block(*block);
        block.name.to_string()
    }
}

impl Dump for (&FuncDef, VarDefRef) {
    fn dump_string(&self) -> String {
        let (func, var) = self;
        func.get_var_def(*var).dump_string()
    }
}

impl Dump for VarDef {
    fn dump_string(&self) -> String {
        let VarDef { name, .. } = self;
        name.to_string()
    }
}

impl Dump for (&TypeContext, &FuncDef, VarDefRef) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, var) = self;
        let VarDef { name, typ } = func.get_var_def(*var);
        format!("{name}: {}", (*ty_ctx, *typ).dump_string())
    }
}

impl Dump for (&TypeContext, &FuncDef, &Operand) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, operand) = self;
        let Operand { typ, val } = operand;
        format!(
            "({} : {})",
            match val.as_ref() {
                OperandEnum::Imm(lit) => lit.dump_string(),
                OperandEnum::Var(var) => (*func, *var).dump_string(),
            },
            (*ty_ctx, *typ).dump_string()
        )
    }
}

impl Dump for (&TypeContext, &FuncDef, &Block) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, block) = self;
        let mut s = "".to_string();
        writeln!(s, "{}:", block.name).unwrap();
        for stmt in &block.stmts {
            writeln!(s, "    {}", (*ty_ctx, *func, stmt).dump_string()).unwrap();
        }
        writeln!(
            s,
            "    {}",
            (*ty_ctx, *func, &block.terminator).dump_string()
        )
        .unwrap();
        s
    }
}

impl Dump for (&TypeContext, &FuncDef, &Terminator) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, term) = self;
        let mut s = "".to_string();
        match term {
            Terminator::Select(val, targets, other) => {
                write!(s, "select {} [", (*ty_ctx, *func, val).dump_string()).unwrap();
                for (idx, target) in targets.iter().enumerate() {
                    if idx != 0 {
                        write!(s, ", ").unwrap();
                    }
                    write!(
                        s,
                        "{} => {}",
                        target.0.dump_string(),
                        (*func, *other).dump_string(),
                    )
                    .unwrap();
                }
                write!(s, ", _ => {}]", (*func, *other).dump_string()).unwrap();
            }
            Terminator::Jump(target) => {
                write!(s, "jump {}", (*func, *target).dump_string()).unwrap();
            }
            Terminator::Return => {
                write!(s, "ret").unwrap();
            }
            Terminator::Panic => {
                write!(s, "panic").unwrap();
            }
            Terminator::Branch(val, t, f) => {
                write!(
                    s,
                    "br {} [{}, {}]",
                    (*ty_ctx, *func, val).dump_string(),
                    (*func, *t).dump_string(),
                    (*func, *f).dump_string()
                )
                .unwrap();
            }
        }
        s
    }
}

impl Dump for (&TypeContext, &FuncDef, &Stmt) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, stmt) = self;
        if let Some(left) = stmt.left {
            format!(
                "{: <24} = {};",
                (*func, left).dump_string(),
                (*ty_ctx, *func, stmt.right.as_ref().unwrap()).dump_string()
            )
        } else {
            format!(
                "{: <24} = {};",
                "_",
                (*ty_ctx, *func, stmt.right.as_ref().unwrap()).dump_string()
            )
        }
    }
}

impl Dump for (&TypeContext, &FuncDef, &Value) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, val) = self;
        let Value { typ, val } = val;

        format!(
            "{} : {}",
            (*ty_ctx, *func, val).dump_string(),
            (*ty_ctx, *typ).dump_string()
        )
    }
}

impl Dump for (&TypeContext, &FuncDef, &Vec<Operand>) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, vec) = self;
        let mut s = "".to_string();
        for (idx, val) in vec.iter().enumerate() {
            if idx != 0 {
                write!(s, " ").unwrap();
            }
            write!(s, "{}", (*ty_ctx, *func, val).dump_string()).unwrap();
        }
        s
    }
}

impl Dump for Vec<String> {
    fn dump_string(&self) -> String {
        self.join(".")
    }
}

impl Dump for (&TypeContext, &FuncDef, &ValueEnum) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, val) = self;
        let mut s = "".to_string();
        match val {
            ValueEnum::Call(path, args) => {
                write!(
                    s,
                    "call {} ({})",
                    path.dump_string(),
                    (*ty_ctx, *func, args).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ExtCall(path, args) => {
                write!(
                    s,
                    "extern-call {} ({})",
                    path.dump_string(),
                    (*ty_ctx, *func, args).dump_string()
                )
                .unwrap();
            }
            ValueEnum::BinaryOp(op, left, right) => {
                write!(
                    s,
                    "{} {} {}",
                    op.dump_string(),
                    (*ty_ctx, *func, left).dump_string(),
                    (*ty_ctx, *func, right).dump_string()
                )
                .unwrap();
            }
            ValueEnum::UnaryOp(op, expr) => {
                write!(
                    s,
                    "{} {}",
                    op.dump_string(),
                    (*ty_ctx, *func, expr).dump_string()
                )
                .unwrap();
            }
            ValueEnum::MakeTuple(args) => {
                write!(s, "gather ({})", (*ty_ctx, *func, args).dump_string()).unwrap();
            }
            ValueEnum::Construct(idx, args) => {
                write!(
                    s,
                    "construct {} ({})",
                    idx,
                    (*ty_ctx, *func, args).dump_string()
                )
                .unwrap();
            }
            ValueEnum::Intrinsic(intrinsic, args) => {
                write!(s, "@{intrinsic} ({})", (*ty_ctx, *func, args).dump_string()).unwrap();
            }
            ValueEnum::Index(arr, idx) => {
                write!(
                    s,
                    "index {} {}",
                    (*ty_ctx, *func, arr).dump_string(),
                    (*ty_ctx, *func, idx).dump_string(),
                )
                .unwrap();
            }

            ValueEnum::Operand(operand) => {
                write!(s, "{}", (*ty_ctx, *func, operand).dump_string()).unwrap();
            }
        }
        s
    }
}

impl Dump for BinOp {
    fn dump_string(&self) -> String {
        (match self {
            BinOp::Plus => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::Div => "div",
            BinOp::Mod => "mod",
            BinOp::Or => "logical-or",
            BinOp::And => "logical-and",
            BinOp::Le => "cmp-le",
            BinOp::Ge => "cmp-ge",
            BinOp::Eq => "cmp-eq",
            BinOp::Ne => "cmp-ne",
            BinOp::Lt => "cmp-lt",
            BinOp::Gt => "cmp-gt",
        })
        .to_string()
    }
}

impl Dump for UnaryOp {
    fn dump_string(&self) -> String {
        (match self {
            UnaryOp::Not => "not",
            UnaryOp::Positive => "pos",
            UnaryOp::Negative => "neg",
        })
        .to_string()
    }
}

impl Dump for MiddleIR {
    fn dump_string(&self) -> String {
        let mut s = "".to_string();
        let ty_ctx_with_all_opaque_recovered = self.ty_ctx.get_display_name_map().0;
        writeln!(s, "{}\n", &ty_ctx_with_all_opaque_recovered).unwrap();
        for func in self.module.iter() {
            let FuncDef {
                name,
                blocks,
                variables: _,
                params,
                locals,
                temporaries,
                obj_reference,
                unwrapped,
                return_value,
                entry_block: _,
                return_block: _,
                panic_block: _,
            } = func;

            writeln!(s, "fn {name} {{").unwrap();
            let mut print_var = |var: VarDefRef| {
                writeln!(
                    s,
                    "    {}",
                    (&ty_ctx_with_all_opaque_recovered, func, var).dump_string()
                )
                .unwrap()
            };

            print_var(return_value.unwrap());
            params.iter().copied().for_each(&mut print_var);
            locals.iter().copied().for_each(&mut print_var);
            temporaries.iter().copied().for_each(&mut print_var);
            obj_reference.iter().copied().for_each(&mut print_var);
            unwrapped.iter().copied().for_each(&mut print_var);

            writeln!(s).unwrap();
            for block in blocks {
                writeln!(
                    s,
                    "{}",
                    (&ty_ctx_with_all_opaque_recovered, func, block.1).dump_string()
                )
                .unwrap();
            }

            writeln!(s, "}}\n").unwrap();
        }
        writeln!(s).unwrap();
        s
    }
}

use slotmap::{new_key_type, SlotMap};
use std::collections::HashSet;
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
    pub captured: Vec<VarDefRef>,
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
    CapturedVariable,
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
    Select(VarDefRef, Vec<(usize, BlockRef)>, BlockRef),
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
    Imm(i32),
    Literal(Literal),
    Var(VarDefRef),
}

#[derive(Debug, Clone)]
pub enum ValueEnum {
    Call(Vec<String>, Vec<Operand>),
    ExtCall(Vec<String>, Vec<Operand>),
    ExtractClosureCapture(VarDefRef, usize),
    ClosureCall(Operand, Vec<Operand>),
    MakeClosure {
        path: Vec<String>,
        capture: Vec<Operand>,
    },
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
    MakeTuple(Vec<Operand>),
    Construct(usize, Vec<Operand>),
    Intrinsic(&'static str, Vec<Operand>),
    Index(Operand, Operand),
    Operand(Operand),
    UnboxedOperand(Operand),
    ExtractTupleField(Operand, usize),
    ExtractEnumField(usize, Operand, usize),
    ExtractEnumTag(Operand),
    CombineByFoldWithAnd1(Vec<Operand>),
    UnboxBool(Operand),
    UnboxInt32(Operand),
    CompareStr(Operand, Literal),
    CompareCInt32(Operand, i32),
    IncreaseIndVar(Operand),
}

#[derive(Debug)]
struct FunctionBuilder<'a> {
    position: Option<BlockRef>,
    namer: UniqueName,
    var_ctx: NameContext<VarDefRef>,
    name_ctx: &'a NameContext<TypeRef>,
    ty_ctx: &'a TypeContext,
    func: &'a mut FuncDef,
    continue_blocks: Vec<BlockRef>,
    break_blocks: Vec<BlockRef>,
    closure_depth: usize,
    anonymous_function: Vec<FuncDef>,
}

#[derive(Debug, Default, Clone)]
pub struct MiddleIR {
    pub name_ctx: NameContext<TypeRef>,
    pub ty_ctx: TypeContext,
    pub module: Vec<FuncDef>,
}

impl FuncDef {
    fn create_variable_definition_with_name(
        &mut self,
        name: String,
        typ: TypeRef,
        kind: VariableKind,
    ) -> VarDefRef {
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
                VariableKind::CapturedVariable => &mut self.captured,
                _ => unreachable!(),
            }
            .push(var_ref);
        }
        var_ref
    }
    fn create_variable_definition(
        &mut self,
        name: Option<&str>,
        namer: &mut UniqueName,
        typ: TypeRef,
        kind: VariableKind,
    ) -> VarDefRef {
        let name = namer.next_name(name.unwrap_or("var"));
        self.create_variable_definition_with_name(name, typ, kind)
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
        name: Option<&str>,
        namer: &mut UniqueName,
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
    const ANONYMOUS_FUNCTION_UUID: uuid::Uuid = uuid::uuid!("67a1aaad-70ab-4107-be56-0a3c3b10ac29");
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
            closure_depth: 0,
            anonymous_function: vec![],
        }
    }

    fn build_function_body(&mut self, body: &TypedBracketBody, ret: VarDefRef) {
        self.build_bracket_body(body, Some(ret));
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

        let new_var = if var_name != "_" {
            Some(self.create_variable(
                Some(var_name.as_str()),
                *var_type,
                VariableKind::LocalVariable,
            ))
        } else {
            None
        };

        self.build_expr_and_assign_to(expr, new_var);
        new_var.and_then(|new_var| self.var_ctx.insert_symbol(var_name.clone(), new_var));
    }

    fn build_bracket_body(&mut self, body: &TypedBracketBody, out: Option<VarDefRef>) {
        self.var_ctx.entry_scope();
        for stmt in &body.stmts {
            self.build_stmt(stmt);
        }
        if let Some(ret_expr) = &body.ret_expr {
            self.build_expr_and_assign_to(ret_expr, out);
        } else if let Some(out) = out {
            self.build_unit_and_assign_to(out);
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
        self.build_bracket_body(body, None);
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

        // this is the induction variable and variable for termination value
        let ind_var =
            self.create_variable(Some(var_name), range_l.typ, VariableKind::LocalVariable);
        let term_value = self.create_variable(
            Some("for.range.terminate"),
            range_r.typ,
            VariableKind::TemporaryVariable,
        );
        // we assign the initial value to the induction variable
        self.build_expr_and_assign_to(range_l, Some(ind_var));
        self.build_expr_and_assign_to(range_r, Some(term_value));

        // allow to find the reference to induction variable
        if var_name != "_" {
            self.var_ctx
                .insert_symbol(var_name.clone(), ind_var)
                .and::<()>(None);
        }

        // move to check block;
        self.position = Some(check_block);

        // this is the test result of equality of induction variable and termination value
        let cond_check_var = self.create_variable(
            Some("for.cond.check"),
            self.ty_ctx.primitive_type(Primitive::Bool),
            VariableKind::TemporaryVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(cond_check_var),
            right: Some(Value {
                typ: self.ty_ctx.primitive_type(Primitive::Bool),
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
            end_block,
            body_block,
        ));

        self.position = Some(body_block);
        self.build_bracket_body(body, None);
        self.change_terminator_at_position(Terminator::Jump(check_block));

        self.insert_stmt_at_position(Stmt {
            left: Some(ind_var),
            right: Some(Value {
                typ: range_l.typ,
                val: ValueEnum::IncreaseIndVar(self.build_operand_from_var_def(ind_var)),
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

        let result = self.create_variable(
            Some("convert"),
            target_type,
            VariableKind::TemporaryVariable,
        );
        self.insert_stmt_at_position(Stmt {
            left: Some(result),
            right: Some(Value {
                typ: target_type,
                val: ValueEnum::Intrinsic("convert", vec![source]),
            }),
            note: "convert type",
        });

        self.build_operand_from_var_def(result)
    }

    fn build_assignee_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        self.check_assignee(expr);
        match expr.expr.as_ref() {
            ExprEnum::Subscript { .. } => self.build_subscript_expr_as_var_def(expr),
            ExprEnum::ClosureCall { .. } => self.build_closure_call_expr_as_var_def(expr),
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
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Closure { param_list, ret_type, body } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        self.closure_depth += 1;

        let mut fv_list = vec![];
        self.collect_free_variables_list_in_expr(body, &mut fv_list, self.closure_depth);

        let fv_list: HashSet<_> = fv_list.into_iter().collect();
        let fv_list: Vec<_> = fv_list.into_iter().collect();

        let closure_var = self.create_variable(Some("closure"), typ, VariableKind::LocalVariable);

        let capture: Vec<_> = fv_list
            .iter()
            .map(|path| {
                self.var_ctx
                    .find_symbol(path)
                    .unwrap_or_else(|| panic!("unable to capture variable {}", path.join(".")))
            })
            .collect();

        let closure_uuid = uuid::Uuid::new_v5(
            &FunctionBuilder::ANONYMOUS_FUNCTION_UUID,
            self.namer
                .next_name(format!("{}@closure", self.func.name).as_str())
                .as_bytes(),
        )
        .simple();

        let closure_function_name = format!("closure_{}", closure_uuid);
        let capture_name_type_list: Vec<_> = fv_list
            .iter()
            .zip(capture.iter())
            .map(|(name, var_def_ref)| {
                let typ = self.get_var_type(*var_def_ref);
                (name[0].to_string(), typ)
            })
            .collect();

        let mut fn_def = self.build_closure_function(
            closure_function_name.as_str(),
            *ret_type,
            param_list,
            body,
            &capture_name_type_list,
        );

        self.anonymous_function.append(&mut fn_def);

        self.insert_stmt_at_position(Stmt {
            left: Some(closure_var),
            right: Some(Value {
                typ,
                val: ValueEnum::MakeClosure {
                    path: vec![closure_function_name],
                    capture: capture
                        .iter()
                        .map(|var| self.build_operand_from_var_def(*var))
                        .collect(),
                },
            }),
            note: "make a closure",
        });

        self.closure_depth -= 1;

        self.build_operand_from_var_def(closure_var)
    }

    fn build_closure_function(
        &mut self,
        name: &str,
        ret_type: TypeRef,
        params: &[TypedBind],
        body: &TypedExpr,
        captured: &[(String, TypeRef)],
    ) -> Vec<FuncDef> {
        let mut def = FuncDef {
            name: name.to_string(),
            ..Default::default()
        };

        // setup the symbol table
        let mut var_ctx: NameContext<VarDefRef> = Default::default();

        // create the return value variable
        let ret_var = def.create_variable_definition_with_name(
            "ret.var".to_string(),
            ret_type,
            VariableKind::ReturnVariable,
        );

        let closure_object = def.create_variable_definition_with_name(
            "closure.self".to_string(),
            self.ty_ctx.primitive_type(Primitive::Object),
            VariableKind::Parameter,
        );

        var_ctx.entry_scope();
        for TypedBind {
            with_at: _,
            var_name,
            typ,
        } in params
        {
            let param = def.create_variable_definition_with_name(
                var_name.to_string(),
                *typ,
                VariableKind::Parameter,
            );
            if var_name != "_" {
                var_ctx
                    .insert_symbol(var_name.to_string(), param)
                    .and_then(|_| -> Option<()> { panic!("parameter redefined") });
            }
        }

        def.initialize_blocks();
        let entry_block = def.entry_block;

        var_ctx.entry_scope();
        let mut fn_builder =
            FunctionBuilder::create(&mut def, entry_block, var_ctx, self.name_ctx, self.ty_ctx);
        fn_builder.initialize_captured_variable(captured, closure_object);
        fn_builder.build_expr_and_assign_to(body, Some(ret_var));

        fn_builder.var_ctx.exit_scope();
        fn_builder.var_ctx.exit_scope();

        let mut other_defs = fn_builder.anonymous_function;
        let mut def_vec = vec![def];
        def_vec.append(&mut other_defs);
        def_vec
    }

    fn initialize_captured_variable(
        &mut self,
        captured: &[(String, TypeRef)],
        closure_object: VarDefRef,
    ) {
        for (idx, captured) in captured.iter().enumerate() {
            let captured_var = self.func.create_variable_definition_with_name(
                captured.0.to_string(),
                captured.1,
                VariableKind::CapturedVariable,
            );
            if captured.0 != "_" {
                self.var_ctx
                    .insert_symbol(captured.0.to_string(), captured_var)
                    .and_then(|_| -> Option<()> { panic!("duplicate capture") });
            }
            self.insert_stmt_at_position(Stmt {
                left: Some(captured_var),
                right: Some(Value {
                    typ: captured.1,
                    val: ValueEnum::ExtractClosureCapture(closure_object, idx),
                }),
                note: "extract captured value from closure",
            })
        }
    }

    fn collect_free_variables_list_in_bracket(
        &self,
        body: &TypedBracketBody,
        out: &mut Vec<Vec<String>>,
        depth: usize,
    ) {
        let TypedBracketBody {
            stmts,
            ret_expr,
            typ: _,
        } = body;
        for stmt in stmts {
            self.collect_free_variables_list_in_stmt(stmt, out, depth);
        }
        if let Some(ret_expr) = ret_expr {
            self.collect_free_variables_list_in_expr(ret_expr, out, depth);
        }
    }

    fn collect_free_variables_list_in_stmt(
        &self,
        stmt: &TypedASTStmt,
        out: &mut Vec<Vec<String>>,
        depth: usize,
    ) {
        match stmt {
            TypedASTStmt::Let(x) => self.collect_free_variables_list_in_expr(&x.expr, out, depth),
            TypedASTStmt::While(x) => {
                let TypedWhileStmt { condition, body } = x.as_ref();
                self.collect_free_variables_list_in_expr(condition, out, depth);
                self.collect_free_variables_list_in_bracket(body, out, depth);
            }
            TypedASTStmt::For(x) => {
                let TypedForStmt {
                    range_l,
                    range_r,
                    body,
                    ..
                } = x.as_ref();
                self.collect_free_variables_list_in_expr(range_l, out, depth);
                self.collect_free_variables_list_in_expr(range_r, out, depth);
                self.collect_free_variables_list_in_bracket(body, out, depth);
            }
            TypedASTStmt::Return => {}
            TypedASTStmt::Break => {}
            TypedASTStmt::Continue => {}
            TypedASTStmt::Asgn(x) => {
                let TypedAsgnStmt { lhs, rhs } = x.as_ref();
                self.collect_free_variables_list_in_expr(lhs, out, depth);
                self.collect_free_variables_list_in_expr(rhs, out, depth);
            }
            TypedASTStmt::Expr(x) => self.collect_free_variables_list_in_expr(x, out, depth),
        }
    }

    fn collect_free_variables_list_in_expr(
        &self,
        expr: &TypedExpr,
        out: &mut Vec<Vec<String>>,
        depth: usize,
    ) {
        let TypedExpr { expr, .. } = expr;
        match expr.as_ref() {
            ExprEnum::Closure { body, .. } => {
                self.collect_free_variables_list_in_expr(body, out, depth + 1)
            }
            ExprEnum::Match { expr, arms } => {
                self.collect_free_variables_list_in_expr(expr, out, depth);
                for arm in arms.iter() {
                    self.collect_free_variables_list_in_expr(&arm.1, out, depth);
                }
            }
            ExprEnum::If {
                condition,
                then,
                or,
            } => {
                self.collect_free_variables_list_in_expr(condition, out, depth);
                self.collect_free_variables_list_in_expr(then, out, depth);
                if let Some(or) = or {
                    self.collect_free_variables_list_in_expr(or, out, depth);
                }
            }
            ExprEnum::BinOp { lhs, rhs, .. } => {
                self.collect_free_variables_list_in_expr(lhs, out, depth);
                self.collect_free_variables_list_in_expr(rhs, out, depth);
            }
            ExprEnum::UnaryOp { expr, .. } => {
                self.collect_free_variables_list_in_expr(expr, out, depth);
            }
            ExprEnum::Subscript { arr, index } => {
                self.collect_free_variables_list_in_expr(arr, out, depth);
                self.collect_free_variables_list_in_expr(index, out, depth);
            }
            ExprEnum::ClosureCall { expr, args } => {
                self.collect_free_variables_list_in_expr(expr, out, depth);
                args.iter()
                    .map(|arg| match arg {
                        TypedArgument::Expr(expr) => expr,
                        TypedArgument::AtVar(_, _) => unimplemented!("not available"),
                    })
                    .for_each(|arg| self.collect_free_variables_list_in_expr(arg, out, depth));
            }
            ExprEnum::CtorCall { args, .. } => {
                args.iter()
                    .map(|arg| match arg {
                        TypedArgument::Expr(expr) => expr,
                        TypedArgument::AtVar(_, _) => unimplemented!("not available"),
                    })
                    .for_each(|arg| self.collect_free_variables_list_in_expr(arg, out, depth));
            }
            ExprEnum::Call { args, .. } => {
                args.iter()
                    .map(|arg| match arg {
                        TypedArgument::Expr(expr) => expr,
                        TypedArgument::AtVar(_, _) => unimplemented!("not available"),
                    })
                    .for_each(|arg| self.collect_free_variables_list_in_expr(arg, out, depth));
            }
            ExprEnum::Tuple { elements } => {
                elements
                    .iter()
                    .for_each(|elem| self.collect_free_variables_list_in_expr(elem, out, depth));
            }
            ExprEnum::Lit(_) => {}
            ExprEnum::Path {
                capture_depth,
                path,
            } => {
                if depth as isize - *capture_depth as isize <= 0 {
                    out.push(path.clone());
                }
            }
            ExprEnum::Bracket(body) => {
                self.collect_free_variables_list_in_bracket(body, out, depth);
            }
        }
    }

    fn build_var_def_from_operand(&mut self, operand: &Operand) -> VarDefRef {
        let Operand { val, typ } = operand;
        let typ = *typ;
        let x = match val.as_ref() {
            OperandEnum::Literal(_) => {
                let tmp = self.create_variable(Some("tmp"), typ, VariableKind::TemporaryVariable);
                self.insert_stmt_at_position(Stmt {
                    left: Some(tmp),
                    right: Some(Value {
                        typ,
                        val: ValueEnum::Operand(operand.clone()),
                    }),
                    note: "insert a tmp variable for match binding",
                });
                tmp
            }
            OperandEnum::Var(var) => *var,
            OperandEnum::Imm(_) => unreachable!(),
        };
        x
    }

    fn build_string_match_expr(
        &mut self,
        matched: Operand,
        arms: &[(TypedASTComplexPattern, TypedExpr)],
        out: VarDefRef,
    ) -> Operand {
        let exhaustive = arms.iter().any(|(pat, _)| {
            use TypedASTComplexPattern::*;
            matches!(pat, Wildcard | Variable(_))
        });

        if !exhaustive {
            panic!("not exhaustive pattern matching");
        }

        self.position.unwrap();
        let old_terminator = self.get_terminator_at_position().clone();
        let end_block = self.create_block(Some("match.end"), Some(old_terminator));

        for (index, (pat, expr)) in arms.iter().enumerate() {
            use crate::ast::Literal::*;
            use TypedASTComplexPattern::*;
            match pat {
                Ctor { .. }
                | Tuple { .. }
                | Literal(Float(_))
                | Literal(Int(_))
                | Literal(Bool(_))
                | Literal(Unit) => {
                    panic!("not a valid pattern for matching integer")
                }
                Literal(x) => {
                    let cmp_res = self.create_variable(
                        Some("str.cmp"),
                        self.ty_ctx.primitive_type(Primitive::CInt32),
                        VariableKind::RawVariable,
                    );

                    // compare the string with the literal in current block
                    self.insert_stmt_at_position(Stmt {
                        left: Some(cmp_res),
                        right: Some(Value {
                            typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                            val: ValueEnum::CompareStr(matched.clone(), x.clone()),
                        }),
                        note: "compare string and returns an i32",
                    });

                    // create next block for possible following comparison
                    let next_try_block =
                        self.create_block(Some("arm.check"), Some(Terminator::Jump(end_block)));

                    // create expr block to do the work of expr
                    let expr_block =
                        self.create_block(Some("arm"), Some(Terminator::Jump(end_block)));

                    self.change_terminator_at_position(Terminator::Branch(
                        self.build_operand_from_var_def(cmp_res),
                        next_try_block,
                        expr_block,
                    ));

                    self.position = Some(expr_block);
                    self.build_expr_and_assign_to(expr, Some(out));

                    self.position = Some(next_try_block);
                }
                Variable(name) => {
                    if index != arms.len() - 1 {
                        panic!(
                            "this variable capture the expression but it's not the last match arm"
                        )
                    }

                    let x = self.build_var_def_from_operand(&matched);

                    self.var_ctx.entry_scope();
                    self.var_ctx
                        .insert_symbol(name.to_string(), x)
                        .and_then(|_| -> Option<()> { unreachable!() });

                    self.build_expr_and_assign_to(expr, Some(out));
                    self.var_ctx.exit_scope();
                }
                Wildcard => {
                    if index != arms.len() - 1 {
                        panic!(
                            "the wildcard capture the expression but it's not the last match arm"
                        )
                    }

                    self.build_expr_and_assign_to(expr, Some(out));
                    self.var_ctx.exit_scope();
                }
            }
        }

        self.position = Some(end_block);
        self.build_operand_from_var_def(out)
    }

    fn build_integer_match_expr(
        &mut self,
        matched: Operand,
        arms: &[(TypedASTComplexPattern, TypedExpr)],
        out: VarDefRef,
    ) -> Operand {
        let exhaustive = arms.iter().any(|(pat, _)| {
            use TypedASTComplexPattern::*;
            matches!(pat, Wildcard | Variable(_))
        });

        if !exhaustive {
            panic!("not exhaustive pattern matching");
        }

        let unboxed_integer = self.create_variable(
            Some("int"),
            self.ty_ctx.primitive_type(Primitive::CInt32),
            VariableKind::RawVariable,
        );

        self.insert_stmt_at_position(Stmt {
            left: Some(unboxed_integer),
            right: Some(Value {
                typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                val: ValueEnum::UnboxInt32(matched.clone()),
            }),
            note: "load a i32 value",
        });

        let mut terminator_other = None;
        let mut choices = vec![];
        let last_block = self.position.unwrap();
        let old_terminator = self.change_terminator_at_position(Terminator::Select(
            unboxed_integer,
            vec![],
            self.func.panic_block,
        ));
        let end_block = self.create_block(Some("match.end"), Some(old_terminator));

        for (index, (pat, expr)) in arms.iter().enumerate() {
            use crate::ast::Literal::*;
            use TypedASTComplexPattern::*;
            match pat {
                Ctor { .. }
                | Tuple { .. }
                | Literal(Float(_))
                | Literal(Str(_))
                | Literal(Bool(_))
                | Literal(Unit) => {
                    panic!("not a valid pattern for matching integer")
                }
                Literal(Int(x)) => {
                    let arm_block =
                        self.create_block(Some("arm"), Some(Terminator::Jump(end_block)));

                    choices.push((*x as usize, arm_block));
                    self.position = Some(arm_block);
                    self.build_expr_and_assign_to(expr, Some(out));
                }
                Variable(name) => {
                    if index != arms.len() - 1 {
                        panic!(
                            "this variable capture the expression but it's not the last match arm"
                        )
                    }

                    let x = self.build_var_def_from_operand(&matched);

                    self.var_ctx.entry_scope();
                    self.var_ctx
                        .insert_symbol(name.to_string(), x)
                        .and_then(|_| -> Option<()> { unreachable!() });

                    let arm_block =
                        self.create_block(Some("arm"), Some(Terminator::Jump(end_block)));
                    terminator_other = Some(arm_block);
                    self.position = Some(arm_block);
                    self.build_expr_and_assign_to(expr, Some(out));
                    self.var_ctx.exit_scope();
                }
                Wildcard => {
                    if index != arms.len() - 1 {
                        panic!(
                            "the wildcard capture the expression but it's not the last match arm"
                        )
                    }

                    let arm_block =
                        self.create_block(Some("arm"), Some(Terminator::Jump(end_block)));
                    terminator_other = Some(arm_block);
                    self.position = Some(arm_block);
                    self.build_expr_and_assign_to(expr, Some(out));
                }
            }
        }

        let other_position = terminator_other.unwrap_or(self.func.panic_block);
        self.position = Some(last_block);
        let term = self.get_terminator_at_position();
        *term = Terminator::Select(unboxed_integer, choices, other_position);

        self.position = Some(end_block);
        self.build_operand_from_var_def(out)
    }

    fn build_pattern_matches_operand_condition_check_and_insert_binding(
        &mut self,
        matched: Operand,
        pat: &TypedASTComplexPattern,
        check_status: VarDefRef,
    ) {
        use TypedASTComplexPattern::*;

        match pat {
            Ctor { name, inner } => {
                let (ctor_idx, types) = self
                    .ty_ctx
                    .get_ctor_index_and_field_type_ref_by_name(matched.typ, name);

                let tag_var = self.create_variable(
                    Some("tag"),
                    self.ty_ctx.primitive_type(Primitive::CInt32),
                    VariableKind::RawVariable,
                );

                self.insert_stmt_at_position(Stmt {
                    left: Some(tag_var),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::ExtractEnumTag(matched.clone()),
                    }),
                    note: "extract the tag from the enum",
                });

                let cmp_var = self.create_variable(
                    Some("cmp.ci32"),
                    self.ty_ctx.primitive_type(Primitive::CInt32),
                    VariableKind::RawVariable,
                );

                self.insert_stmt_at_position(Stmt {
                    left: Some(cmp_var),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::CompareCInt32(
                            self.build_operand_from_var_def(tag_var),
                            ctor_idx as i32,
                        ),
                    }),
                    note: "compare tag and pattern",
                });

                let current = self.get_terminator_at_position().clone();

                let check_end_block =
                    self.create_block(Some("match.arm.check.ctor.end"), Some(current));

                let check_succeeded_block = self.create_block(
                    Some("match.arm.check.ctor.succeeded"),
                    Some(Terminator::Jump(check_end_block)),
                );

                let check_failed_block = self.create_block(
                    Some("match.arm.check.ctor.failed"),
                    Some(Terminator::Jump(check_end_block)),
                );

                self.change_terminator_at_position(Terminator::Branch(
                    self.build_operand_from_var_def(cmp_var),
                    check_succeeded_block,
                    check_failed_block,
                ));

                let check_inner_result_var: Vec<_> = inner
                    .iter()
                    .map(|_| {
                        self.create_variable(
                            Some("check.inner.res"),
                            self.ty_ctx.primitive_type(Primitive::CInt32),
                            VariableKind::RawVariable,
                        )
                    })
                    .collect();

                // ctor check passed, remain its all fields to be checked
                self.position = Some(check_succeeded_block);
                for (index, ((inner, typ), res)) in inner
                    .iter()
                    .zip(types)
                    .zip(check_inner_result_var.iter())
                    .enumerate()
                {
                    let ctor_field = self.create_variable(
                        Some("ctor.field"),
                        typ,
                        VariableKind::TemporaryVariable,
                    );

                    self.insert_stmt_at_position(Stmt {
                        left: Some(ctor_field),
                        right: Some(Value {
                            typ,
                            val: ValueEnum::ExtractEnumField(ctor_idx, matched.clone(), index),
                        }),
                        note: "extract the field of ctor",
                    });

                    self.build_pattern_matches_operand_condition_check_and_insert_binding(
                        self.build_operand_from_var_def(ctor_field),
                        inner,
                        *res,
                    )
                }

                let check_inner_result = check_inner_result_var
                    .iter()
                    .copied()
                    .map(|x| self.build_operand_from_var_def(x))
                    .collect();
                self.insert_stmt_at_position(Stmt {
                    left: Some(check_status),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::CombineByFoldWithAnd1(check_inner_result),
                    }),
                    note: "combine multiple conditions into one",
                });

                // ctor check didn't pass
                self.position = Some(check_failed_block);
                self.insert_stmt_at_position(Stmt {
                    left: Some(check_status),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::UnboxedOperand(self.build_operand_from_imm(0)),
                    }),
                    note: "check not passed",
                });

                self.position = Some(check_end_block);
            }
            Tuple { fields } => {
                let current = self.get_terminator_at_position().clone();

                let check_end_block =
                    self.create_block(Some("match.arm.check.tuple.end"), Some(current));

                self.change_terminator_at_position(Terminator::Jump(check_end_block));

                let check_field_result_var: Vec<_> = fields
                    .iter()
                    .map(|_| {
                        self.create_variable(
                            Some("check.field.res"),
                            self.ty_ctx.primitive_type(Primitive::CInt32),
                            VariableKind::RawVariable,
                        )
                    })
                    .collect();

                let types = self.ty_ctx.get_tuple_field_type_ref(matched.typ);
                for (index, ((field, typ), res)) in fields
                    .iter()
                    .zip(types)
                    .zip(check_field_result_var.iter())
                    .enumerate()
                {
                    let tuple_field = self.create_variable(
                        Some("tuple.field"),
                        typ,
                        VariableKind::TemporaryVariable,
                    );

                    self.insert_stmt_at_position(Stmt {
                        left: Some(tuple_field),
                        right: Some(Value {
                            typ,
                            val: ValueEnum::ExtractTupleField(matched.clone(), index),
                        }),
                        note: "extract the field of tuple",
                    });

                    self.build_pattern_matches_operand_condition_check_and_insert_binding(
                        self.build_operand_from_var_def(tuple_field),
                        field,
                        *res,
                    )
                }

                let check_field_result = check_field_result_var
                    .iter()
                    .copied()
                    .map(|x| self.build_operand_from_var_def(x))
                    .collect();

                self.insert_stmt_at_position(Stmt {
                    left: Some(check_status),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::CombineByFoldWithAnd1(check_field_result),
                    }),
                    note: "combine multiple conditions into one",
                });

                self.position = Some(check_end_block);
            }
            Literal(lit) => {
                let result = self.create_variable(
                    Some("match.lit.cmp.res"),
                    self.ty_ctx.primitive_type(Primitive::Bool),
                    VariableKind::TemporaryVariable,
                );

                self.insert_stmt_at_position(Stmt {
                    left: Some(result),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::Bool),
                        val: ValueEnum::BinaryOp(
                            BinOp::Eq,
                            matched,
                            self.build_operand_from_literal(lit.clone()),
                        ),
                    }),
                    note: "compare",
                });

                self.insert_stmt_at_position(Stmt {
                    left: Some(check_status),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::UnboxBool(self.build_operand_from_var_def(result)),
                    }),
                    note: "unbox normal compare result",
                });
            }
            Variable(x) => {
                if x != "_" {
                    let var = self.build_var_def_from_operand(&matched);
                    self.var_ctx
                        .insert_symbol(x.clone(), var)
                        .and_then(|_| -> Option<()> { panic!("duplicate variable binding") });
                }
                self.insert_stmt_at_position(Stmt {
                    left: Some(check_status),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::UnboxedOperand(self.build_operand_from_imm(1)),
                    }),
                    note: "check passed",
                });
            }
            Wildcard => {
                self.insert_stmt_at_position(Stmt {
                    left: Some(check_status),
                    right: Some(Value {
                        typ: self.ty_ctx.primitive_type(Primitive::CInt32),
                        val: ValueEnum::UnboxedOperand(self.build_operand_from_imm(1)),
                    }),
                    note: "check passed",
                });
            }
        }
    }

    fn build_complex_match_expr(
        &mut self,
        matched: Operand,
        arms: &[(TypedASTComplexPattern, TypedExpr)],
        out: VarDefRef,
    ) -> Operand {
        let old_terminator = self.get_terminator_at_position().clone();
        let end_block = self.create_block(Some("match.end"), Some(old_terminator));

        for (pat, expr) in arms.iter() {
            let check = self.create_variable(
                Some("match.check.arm"),
                self.ty_ctx.primitive_type(Primitive::CInt32),
                VariableKind::RawVariable,
            );

            self.var_ctx.entry_scope();
            self.build_pattern_matches_operand_condition_check_and_insert_binding(
                matched.clone(),
                pat,
                check,
            );

            // create next block for possible following comparison
            let next_try_block = self.create_block(Some("arm.check"), None);

            // create expr block to do the work of expr
            let expr_block = self.create_block(Some("arm"), Some(Terminator::Jump(end_block)));

            self.change_terminator_at_position(Terminator::Branch(
                self.build_operand_from_var_def(check),
                expr_block,
                next_try_block,
            ));

            self.position = Some(expr_block);
            self.build_expr_and_assign_to(expr, Some(out));

            self.var_ctx.exit_scope();
            self.position = Some(next_try_block);
        }

        // non-exhaustive
        self.change_terminator_at_position(Terminator::Panic);

        self.position = Some(end_block);
        self.build_operand_from_var_def(out)
    }

    fn build_match_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Match { expr, arms  } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let matched_expr = self.build_expr_as_operand(expr);
        let out = self.create_variable(Some("match.out"), typ, VariableKind::TemporaryVariable);
        match self.get_type(expr.typ) {
            Type::Tuple { .. } | Type::Enum { .. } => {
                self.build_complex_match_expr(matched_expr, arms, out)
            }
            Type::Primitive(x) => match x {
                Primitive::Object => unreachable!(),
                Primitive::Unit => panic!("it's useless to match a unit type"),
                Primitive::Str => self.build_string_match_expr(matched_expr, arms, out),
                Primitive::Bool => unimplemented!("bool match not available"),
                Primitive::Int32 => self.build_integer_match_expr(matched_expr, arms, out),
                Primitive::Float64 => panic!("can't match float type"),
                Primitive::CInt32 => unreachable!(),
            },
            Type::Opaque { .. } => unreachable!("opaque should has been eliminated"),
            Type::Reference { .. } => unimplemented!("reference match not available"),
            Type::Array(_) => unimplemented!("array match not available"),
            Type::Callable { .. } => panic!("can't match a callable value"),
        }
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

        let if_out = self.create_variable(Some("if.res"), typ, VariableKind::TemporaryVariable);

        self.position.unwrap();
        let old_terminator_of_last_block =
            self.change_terminator_at_position(Terminator::Jump(cond_block));

        self.position = Some(cond_block);
        let cond_check_var = self.create_variable(
            Some("if.cond.check"),
            self.ty_ctx.primitive_type(Primitive::Bool),
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

        let mut left_operand = self.build_expr_as_operand(lhs);
        let mut right_operand = self.build_expr_as_operand(rhs);
        let t1 = left_operand.typ;
        let t2 = right_operand.typ;

        if t1 != t2 {
            assert!(self.ty_ctx.is_arithmetic_type(t1));
            assert!(self.ty_ctx.is_arithmetic_type(t2));

            let promoted = self.ty_ctx.determine_promoted_type(t1, t2);
            left_operand = self.build_type_conversion_if_need(left_operand, promoted);
            right_operand = self.build_type_conversion_if_need(right_operand, promoted);
        }

        let result = self.create_variable(Some("bin.op.res"), typ, VariableKind::TemporaryVariable);

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

        let result = self.create_variable(Some("un.op.res"), typ, VariableKind::TemporaryVariable);

        self.insert_stmt_at_position(Stmt {
            left: Some(result),
            right: Some(Value {
                typ,
                val: ValueEnum::UnaryOp(*op, operand),
            }),
            note: "unary operation",
        });

        self.build_operand_from_var_def(result)
    }

    fn build_subscript_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Subscript { arr, index } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let arr = self.build_expr_as_operand(arr);
        let index = self.build_expr_as_operand(index);
        let result = self.create_variable(Some("elem"), typ, VariableKind::ObjectReference);

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
        let call_result = self.build_closure_call_expr_as_var_def(expr);
        self.build_operand_from_var_def(call_result)
    }

    fn build_closure_call_expr_as_var_def(&mut self, expr: &TypedExpr) -> VarDefRef {
        let TypedExpr { expr, .. } = expr;
        let ExprEnum::ClosureCall { expr, args  } = expr.as_ref() else { unreachable!() };

        let closure = self.build_expr_as_operand(expr);

        let Type::Callable { kind , ret_type, parameters } = self.ty_ctx.get_type_by_ref(expr.typ) else {
            unreachable!();
        };

        if kind != CallKind::ClosureValue {
            panic!("internal error");
        }

        let args_operands = self.build_arguments(args, &parameters);

        let call_result =
            self.create_variable(Some("call.res"), ret_type, VariableKind::TemporaryVariable);

        self.insert_stmt_at_position(Stmt {
            left: Some(call_result),
            right: Some(Value {
                typ: ret_type,
                val: ValueEnum::ClosureCall(closure, args_operands),
            }),
            note: "make a closure call here",
        });

        call_result
    }

    fn build_constructor_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::CtorCall { name, args  } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let (ctor_index, params_type) = self
            .ty_ctx
            .get_ctor_index_and_field_type_ref_by_name(typ, name);
        let args_value = self.build_arguments(args, &params_type);

        let construction_result =
            self.create_variable(Some("enum"), typ, VariableKind::TemporaryVariable);

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

        let call_result =
            self.create_variable(Some("call.res"), ret_type, VariableKind::TemporaryVariable);

        self.insert_stmt_at_position(Stmt {
            left: Some(call_result),
            right: Some(Value {
                typ: ret_type,
                val: ValueEnum::Call(self.name_ctx.get_full_symbol_path(path), args_operands),
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
                    let arg_var = self.create_variable(
                        Some("arg"),
                        type_ref,
                        VariableKind::TemporaryVariable,
                    );

                    self.build_expr_and_assign_to(expr, Some(arg_var));
                    vec.push(self.build_operand_from_var_def(arg_var));
                }
                TypedArgument::AtVar(_, _) => {
                    unimplemented!("not available");
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
            let field = self.create_variable(
                Some("tuple.field"),
                element.typ,
                VariableKind::TemporaryVariable,
            );
            fields.push(self.build_operand_from_var_def(field));
            self.build_expr_and_assign_to(element, Some(field));
        }

        let tuple = self.create_variable(Some("tuple"), typ, VariableKind::TemporaryVariable);

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
            val: Box::new(OperandEnum::Literal(lit.clone())),
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

        self.var_ctx
            .find_symbol(path)
            .unwrap_or_else(|| panic!("variable {} not defined", path.join(".")))
    }

    fn build_bracket_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Bracket (body) = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let output_var = self.create_variable(Some("out"), typ, VariableKind::TemporaryVariable);

        self.build_bracket_body(body, Some(output_var));
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

    fn build_operand_from_literal(&self, literal: Literal) -> Operand {
        let typ = match literal {
            Literal::Float(_) => self.ty_ctx.primitive_type(Primitive::Float64),
            Literal::Int(_) => self.ty_ctx.primitive_type(Primitive::Int32),
            Literal::Str(_) => self.ty_ctx.primitive_type(Primitive::Str),
            Literal::Bool(_) => self.ty_ctx.primitive_type(Primitive::Bool),
            Literal::Unit => self.ty_ctx.primitive_type(Primitive::Unit),
        };
        Operand {
            typ,
            val: Box::new(OperandEnum::Literal(literal)),
        }
    }

    fn build_operand_from_imm(&self, imm: i32) -> Operand {
        Operand {
            typ: self.ty_ctx.primitive_type(Primitive::CInt32),
            val: Box::new(OperandEnum::Imm(imm)),
        }
    }

    fn build_unit_and_assign_to(&mut self, output_var: VarDefRef) {
        self.build_expr_and_assign_to(
            &TypedExpr {
                expr: Box::new(ExprEnum::Lit(Literal::Unit)),
                typ: self.ty_ctx.primitive_type(Primitive::Unit),
            },
            Some(output_var),
        );
    }

    fn get_var_type(&self, var_def: VarDefRef) -> TypeRef {
        self.func.get_var_type(var_def)
    }

    fn create_block(&mut self, name: Option<&str>, term: Option<Terminator>) -> BlockRef {
        self.func.create_block(name, &mut self.namer, term)
    }

    fn create_variable(
        &mut self,
        name: Option<&str>,
        typ: TypeRef,
        kind: VariableKind,
    ) -> VarDefRef {
        self.func
            .create_variable_definition(name, &mut self.namer, typ, kind)
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

    fn get_terminator_at_position(&mut self) -> &mut Terminator {
        let block_ref = self.position.expect("expect a insert position");
        let block = self.func.blocks.get_mut(block_ref).unwrap();
        &mut block.terminator
    }

    fn get_type(&self, type_ref: TypeRef) -> Type {
        self.ty_ctx.get_type_by_ref(type_ref)
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
        self.name_ctx.entry_scope();
        for func in fn_def {
            self.insert_fn_signature(func);
        }
        for func in fn_def {
            let mut new_def = self.convert_fn_definition(func);
            self.module.append(&mut new_def);
        }
        self.name_ctx.exit_scope();
    }

    fn insert_fn_signature(&mut self, func: &TypedFuncDef) {
        // insert function type to the name context
        let fn_type = self.ty_ctx.callable_type(
            CallKind::Function,
            func.ret_type,
            func.params
                .iter()
                .map(
                    |TypedBind {
                         with_at: _,
                         var_name: _,
                         typ,
                     }| *typ,
                )
                .collect(),
            false,
        );
        self.name_ctx
            .insert_symbol(func.name.clone(), fn_type)
            .and_then(|_| -> Option<()> { panic!("function {} redefined", func.name) });
    }

    fn convert_fn_definition(&mut self, func: &TypedFuncDef) -> Vec<FuncDef> {
        let mut def = FuncDef {
            name: func.name.clone(),
            ..Default::default()
        };

        // setup the symbol table
        let mut var_ctx: NameContext<VarDefRef> = Default::default();

        // create the return value variable
        let ret_var = def.create_variable_definition_with_name(
            "ret.var".to_string(),
            func.ret_type,
            VariableKind::ReturnVariable,
        );

        let mut params_type = vec![];
        var_ctx.entry_scope();
        for TypedBind {
            with_at: _,
            var_name,
            typ,
        } in &func.params
        {
            let param = def.create_variable_definition_with_name(
                var_name.clone(),
                *typ,
                VariableKind::Parameter,
            );
            params_type.push(*typ);
            if var_name != "_" {
                var_ctx
                    .insert_symbol(var_name.to_string(), param)
                    .and_then(|_| -> Option<()> { panic!("parameter redefined") });
            }
        }

        def.initialize_blocks();
        let entry_block = def.entry_block;
        let mut fn_builder =
            FunctionBuilder::create(&mut def, entry_block, var_ctx, &self.name_ctx, &self.ty_ctx);

        // convert the function body
        fn_builder.build_function_body(&func.body, ret_var);

        // exit the symbol table scope
        fn_builder.var_ctx.exit_scope();

        let mut other_defs = fn_builder.anonymous_function;
        let mut def_vec = vec![def];
        def_vec.append(&mut other_defs);
        def_vec
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
                OperandEnum::Literal(lit) => lit.dump_string(),
                OperandEnum::Var(var) => (*func, *var).dump_string(),
                OperandEnum::Imm(x) => x.to_string(),
            },
            (*ty_ctx, *typ).dump_string()
        )
    }
}

impl Dump for (&TypeContext, &FuncDef, &Block) {
    fn dump_string(&self) -> String {
        let (ty_ctx, func, block) = self;
        let mut s = "".to_string();
        writeln!(s, "[{}]:", block.name).unwrap();
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
                write!(s, "select {} [", (*func, *val).dump_string()).unwrap();
                for (idx, target) in targets.iter().enumerate() {
                    if idx != 0 {
                        write!(s, ", ").unwrap();
                    }
                    write!(s, "{} => {}", target.0, (*func, target.1).dump_string(),).unwrap();
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
                    "call {:?} ({})",
                    path.dump_string(),
                    (*ty_ctx, *func, args).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ExtCall(path, args) => {
                write!(
                    s,
                    "extern-call {:?} ({})",
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
            ValueEnum::UnboxedOperand(operand) => {
                write!(s, "{}", (*ty_ctx, *func, operand).dump_string()).unwrap();
            }
            ValueEnum::MakeClosure { path, capture } => {
                write!(
                    s,
                    "make-closure {:?} capture {}",
                    path,
                    (*ty_ctx, *func, capture).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ExtractClosureCapture(var, index) => {
                write!(
                    s,
                    "extract-captured {}[{index}]",
                    (*func, *var).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ClosureCall(closure, args) => {
                write!(
                    s,
                    "closure-call {} ({}, {})",
                    (*ty_ctx, *func, closure).dump_string(),
                    (*ty_ctx, *func, closure).dump_string(),
                    (*ty_ctx, *func, args).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ExtractTupleField(var, idx) => {
                write!(
                    s,
                    "extract-tuple-field {}[{idx}]",
                    (*ty_ctx, *func, var).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ExtractEnumField(ctor_idx, var, idx) => {
                write!(
                    s,
                    "extract-enum-field {} at {ctor_idx}[{idx}]",
                    (*ty_ctx, *func, var).dump_string()
                )
                .unwrap();
            }
            ValueEnum::ExtractEnumTag(var) => {
                write!(
                    s,
                    "extract-enum-tag {}",
                    (*ty_ctx, *func, var).dump_string()
                )
                .unwrap();
            }
            ValueEnum::CombineByFoldWithAnd1(vec) => {
                write!(
                    s,
                    "fold-with-and-1 ({})",
                    (*ty_ctx, *func, vec).dump_string()
                )
                .unwrap();
            }
            ValueEnum::UnboxBool(val) => {
                write!(s, "unbox-bool {}", (*ty_ctx, *func, val).dump_string(),).unwrap();
            }
            ValueEnum::UnboxInt32(val) => {
                write!(s, "unbox-int32 {}", (*ty_ctx, *func, val).dump_string(),).unwrap();
            }
            ValueEnum::CompareStr(op1, op2) => {
                write!(
                    s,
                    "cmp-str {} {}",
                    (*ty_ctx, *func, op1).dump_string(),
                    op2.dump_string()
                )
                .unwrap();
            }
            ValueEnum::CompareCInt32(op1, op2) => {
                write!(
                    s,
                    "cmp-ci32 {} {}",
                    (*ty_ctx, *func, op1).dump_string(),
                    op2
                )
                .unwrap();
            }
            ValueEnum::IncreaseIndVar(op) => {
                write!(s, "inc {}", (*ty_ctx, *func, op).dump_string(),).unwrap()
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
                captured,
            } = func;

            writeln!(s, "fn {name} {{").unwrap();
            let mut print_var = |var: VarDefRef, prefix: &'static str| {
                writeln!(
                    s,
                    "    {prefix}{}",
                    (&ty_ctx_with_all_opaque_recovered, func, var).dump_string()
                )
                .unwrap()
            };

            print_var(return_value.unwrap(), "#");
            params.iter().copied().for_each(|x| print_var(x, "#"));
            captured.iter().copied().for_each(|x| print_var(x, "^"));
            locals.iter().copied().for_each(|x| print_var(x, "$"));
            temporaries.iter().copied().for_each(|x| print_var(x, "$"));
            obj_reference
                .iter()
                .copied()
                .for_each(|x| print_var(x, "@"));
            unwrapped.iter().copied().for_each(|x| print_var(x, "~"));

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

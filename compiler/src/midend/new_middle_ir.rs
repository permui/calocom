use slotmap::{new_key_type, SlotMap};
use std::fmt::Display;
use std::{panic, vec};

use super::typed_ast::*;
use crate::common::name_context::NameContext;
use crate::common::type_context::*;
use crate::common::unique_name::*;

type RefPath = TypedASTRefPath;
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
    Intrinsic(&'static str, Vec<Operand>),
    Index(Operand),
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
    pub collected_closure: Vec<&'a TypedExpr>,
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
        self.return_block = self.blocks.insert(Block {
            name: "exit".to_string(),
            terminator: Terminator::Return,
            stmts: vec![],
        });

        self.entry_block = self.blocks.insert(Block {
            name: "entry".to_string(),
            terminator: Terminator::Jump(self.return_block),
            stmts: vec![],
        });

        self.panic_block = self.blocks.insert(Block {
            name: "panic".to_string(),
            terminator: Terminator::Panic,
            stmts: vec![],
        });
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
            collected_closure: vec![],
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
        // cond block   <======|
        // ...                 |
        // cond end block -+   |
        //                 |   |
        // body block   <--|   |
        // ...             |   |
        // body end block =|===+
        //                 |
        // end block    <--|   <-- position

        let cond_block = self.create_block(Some("while.cond.start"), None);
        let end_block = self.create_block(Some("while.end"), None);
        let body_block = self.create_block(Some("while.body.start"), None);

        self.continue_blocks.push(cond_block);
        self.break_blocks.push(end_block);

        // record current block and its terminator
        // update its terminator to jump to the condition block
        let last_block = self.position.unwrap();
        let old_terminator_of_last_block =
            self.change_terminator_at_position(Terminator::Jump(cond_block));

        // start codegen of conditional part
        self.position = Some(cond_block);
        let cond_operand = self.build_expr_as_operand(condition);
        assert!(self.ty_ctx.is_boolean_testable_type(cond_operand.typ));

        // record the end block of the condition part
        // update its terminator to branch to body block or end block
        let cond_end_block = self.position.unwrap();
        self.change_terminator_at_position(Terminator::Branch(cond_operand, body_block, end_block));

        // start codegen of body part
        // change its terminator to loop back to the cond block
        self.position = Some(body_block);
        self.build_bracket(body, None);
        self.change_terminator_at_position(Terminator::Jump(cond_block));

        // move to end block
        // change its terminator to the old terminator of last block
        self.position = Some(end_block);
        self.change_terminator_at_position(old_terminator_of_last_block);

        self.continue_blocks.pop();
        self.break_blocks.pop();
    }

    fn build_for(&mut self, stmt: &TypedForStmt) {
        todo!()
    }

    fn build_asgn(&mut self, stmt: &TypedAsgnStmt) {
        let TypedAsgnStmt { lhs, rhs } = stmt;
        let place = self.build_assignee_expr_as_var_def_ref(lhs);
        self.build_expr_and_assign_to(rhs, Some(place));
    }

    fn build_expr_as_operand(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr {
            expr: expr_enum,
            typ,
        } = expr;
        let expr_enum = expr_enum.as_ref();
        let operand = match expr_enum {
            ExprEnum::Closure {
                param_list,
                ret_type,
                body,
            } => self.build_closure_expr(expr),
            ExprEnum::Match { expr, arms } => self.build_match_expr(expr),
            ExprEnum::If {
                condition,
                then,
                or,
            } => self.build_if_expr(expr),
            ExprEnum::BinOp { lhs, rhs, op } => self.build_binary_operation_expr(expr),
            ExprEnum::UnaryOp { expr, op } => self.build_unary_operation_expr(expr),
            ExprEnum::Subscript { arr, index } => self.build_subscript_expr(expr),
            ExprEnum::ClosureCall { expr, args } => self.build_closure_call_expr(expr),
            ExprEnum::Ctor { name, args } => self.build_constructor_expr(expr),
            ExprEnum::Call { path, gen, args } => self.build_call_expr(expr),
            ExprEnum::Tuple { elements } => self.build_tuple_expr(expr),
            ExprEnum::Lit(_) => self.build_literal_expr(expr),
            ExprEnum::Path {
                is_free_variable,
                path,
            } => self.build_path_expr(expr),
            ExprEnum::Bracket { stmts, ret_expr } => self.build_bracket_expr(expr),
        };

        operand
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
        todo!()
    }

    fn build_assignee_expr_as_var_def_ref(&mut self, expr: &TypedExpr) -> VarDefRef {
        self.check_assignee(expr);
        match expr.expr.as_ref() {
            ExprEnum::Subscript { arr, index } => todo!(),
            ExprEnum::ClosureCall { expr, args } => todo!(),
            ExprEnum::Call { path, gen, args } => todo!(),
            ExprEnum::Path {
                is_free_variable,
                path,
            } => todo!(),
            _ => unreachable!("check assignee missed"),
        }
    }

    fn check_assignee(&mut self, expr: &TypedExpr) {
        match expr.expr.as_ref() {
            ExprEnum::Closure {
                param_list,
                ret_type,
                body,
            } => panic!("closure isn't assignable"),
            ExprEnum::Match { expr, arms } => panic!("match expression isn't assignable"),
            ExprEnum::If {
                condition,
                then,
                or,
            } => panic!("if expression isn't assignable"),
            ExprEnum::BinOp { lhs, rhs, op } => {
                panic!("binary operation expression isn't assignable")
            }
            ExprEnum::UnaryOp { expr, op } => panic!("unary operation expression isn't assignable"),
            ExprEnum::Ctor { name, args } => panic!("constructor expression isn't assignable"),
            ExprEnum::Tuple { elements } => panic!("tuple expression isn't assignable"),
            ExprEnum::Lit(_) => panic!("literal isn't assignable"),
            ExprEnum::Bracket { stmts, ret_expr } => panic!("block expression isn't assignable"),
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
        todo!()
    }

    fn build_binary_operation_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_unary_operation_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_subscript_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_closure_call_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_constructor_expr(&mut self, expr: &TypedExpr) -> Operand {
        todo!()
    }

    fn build_call_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Call { path, gen, args  } = expr.as_ref() else { unreachable!() };

        let fn_type = self
            .name_ctx
            .find_symbol(path)
            .unwrap_or_else(|| panic!("can't found function {}", path.join(".")));

        let Type::Callable { kind , ret_type, parameters } = self.ty_ctx.get_type_by_ref(fn_type) else {
            unreachable!();
        };

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

        self.build_operand_from_var_def(call_result)
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
                    let name = self.namer.next_name("at_arg");
                    let arg_var = self.func.create_variable_definition(
                        name.as_str(),
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
        todo!()
    }

    fn build_bracket_expr(&mut self, expr: &TypedExpr) -> Operand {
        let TypedExpr { expr, typ } = expr;
        let ExprEnum::Bracket { stmts, ret_expr } = expr.as_ref() else { unreachable!() };
        let typ = *typ;

        let output_var = self.func.create_variable_definition(
            "bracket.out",
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
            self.build_expr_and_assign_to(
                &TypedExpr {
                    expr: Box::new(ExprEnum::Lit(Literal::Unit)),
                    typ: self.ty_ctx.singleton_type(Primitive::Unit),
                },
                Some(output_var),
            );
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

    fn build_value_from_var_def(&self, var_def: VarDefRef) -> Value {
        let operand = self.build_operand_from_var_def(var_def);
        self.build_value_from_operand(operand)
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

    fn get_var_type(&self, var_def: VarDefRef) -> TypeRef {
        self.func.variables.get(var_def).unwrap().typ
    }

    fn get_block(&self, block_ref: BlockRef) -> &Block {
        self.func.blocks.get(block_ref).unwrap()
    }

    fn create_block(&mut self, name: Option<&str>, term: Option<Terminator>) -> BlockRef {
        self.func.blocks.insert(Block::new(
            &mut self.namer,
            name,
            vec![],
            term.unwrap_or(Terminator::Panic),
        ))
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
        var_ctx.insert_symbol("ret.var".to_string(), ret_var);

        for TypedBind {
            with_at: _,
            var_name,
            typ,
        } in &func.params
        {
            let name = format!("#{}", var_name);
            let param =
                def.create_variable_definition(name.as_str(), *typ, VariableKind::Parameter);

            var_ctx.insert_symbol(var_name.to_string(), param);
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
}

use std::{panic, vec};

use crate::common::{
    name_context::NameContext,
    type_context::{CallKind, Primitive, Type, TypeContext, TypeRef},
};

#[derive(Debug)]
pub struct TypedFuncDef {
    pub name: String,
    pub ret_type: TypeRef,
    pub params: Vec<TypedBind>,
    pub body: Box<TypedBracketBody>,
}

#[derive(Debug)]
pub struct TypedBind {
    pub with_at: bool,
    pub var_name: String,
    pub typ: TypeRef,
}

#[derive(Debug)]
pub struct TypedBracketBody {
    pub stmts: Vec<TypedASTStmt>,
    pub ret_expr: Option<TypedExpr>,
    pub typ: TypeRef,
}

#[derive(Debug)]
pub struct TypedLetStmt {
    pub var_name: String,
    pub var_type: TypeRef,
    pub expr: TypedExpr,
}

#[derive(Debug)]
pub struct TypedAsgnStmt {
    pub lhs: TypedExpr,
    pub rhs: TypedExpr,
}

#[derive(Debug)]
pub struct TypedWhileStmt {
    pub condition: TypedExpr,
    pub body: Box<TypedBracketBody>,
}

#[derive(Debug)]
pub struct TypedForStmt {
    pub var_name: String,
    pub range_l: TypedExpr,
    pub range_r: TypedExpr,
    pub body: Box<TypedBracketBody>,
}

#[derive(Debug)]
pub enum TypedASTStmt {
    Let(Box<TypedLetStmt>),
    While(Box<TypedWhileStmt>),
    For(Box<TypedForStmt>),
    Return,
    Break,
    Continue,
    Asgn(Box<TypedAsgnStmt>),
    Expr(Box<TypedExpr>),
}

#[derive(Debug)]
pub struct TypedExpr {
    pub expr: Box<ExprEnum>,
    pub typ: TypeRef,
}

#[derive(Debug)]
pub enum ExprEnum {
    Closure {
        param_list: Vec<TypedBind>,
        ret_type: TypeRef,
        body: TypedExpr,
    },
    Match {
        expr: TypedExpr,
        arms: Vec<(TypedASTComplexPattern, TypedExpr)>,
    },
    If {
        condition: TypedExpr,
        then: TypedExpr,
        or: Option<TypedExpr>,
    },
    BinOp {
        lhs: TypedExpr,
        rhs: TypedExpr,
        op: TypedASTBinOp,
    },
    UnaryOp {
        expr: TypedExpr,
        op: TypedASTUnaryOp,
    },
    Subscript {
        arr: TypedExpr,
        index: TypedExpr,
    },
    ClosureCall {
        expr: TypedExpr,
        args: Vec<TypedArgument>,
    },
    CtorCall {
        name: String,
        args: Vec<TypedArgument>,
    },
    Call {
        path: Vec<String>,
        args: Vec<TypedArgument>,
    },
    Tuple {
        elements: Vec<TypedExpr>,
    },
    Lit(TypedASTLiteral),
    Path {
        is_free_variable: bool,
        path: Vec<String>,
    },
    Bracket {
        stmts: Vec<TypedASTStmt>,
        ret_expr: Option<TypedExpr>,
    },
}

#[derive(Debug, Clone)]
pub enum TypedASTComplexPattern {
    Ctor {
        name: String,
        inner: Vec<TypedASTComplexPattern>,
    },
    Tuple {
        fields: Vec<TypedASTComplexPattern>,
    },
    Literal(TypedASTLiteral),
    Variable(String),
    Wildcard,
}

#[derive(Debug)]
pub enum TypedArgument {
    Expr(TypedExpr),
    AtVar(String, TypeRef),
}

pub type TypedASTBinOp = crate::ast::BinOp;
pub type TypedASTUnaryOp = crate::ast::UnaryOp;
pub type TypedASTLiteral = crate::ast::Literal;
pub type TypedASTRefPath = crate::ast::RefPath;

#[derive(Debug)]
pub struct TypedASTConstructorVar {
    pub name: String,
    pub inner: Option<String>,
}

#[derive(Debug, Default)]
pub struct TypedAST {
    pub name_ctx: NameContext<TypeRef>,
    pub ty_ctx: TypeContext,
    pub delimiter: Vec<isize>, // the start symbol depth stack of a lambda expression
    pub module: Vec<TypedFuncDef>,
}

macro_rules! declare_library_function {
    ($name_ctx: expr, $ty_ctx: expr; $($fn_name: ident).+ : || => $ret_type: ident) => {
        $name_ctx
            .insert_fully_qualified_symbol(
                [$(stringify!($fn_name)),+].map(|s| s.to_string()).to_vec(),
                $ty_ctx.callable_type(CallKind::Function, $ret_type, [].to_vec()),
            )
            .and_then(|_| -> Option<()> { unreachable!() });
    };
    ($name_ctx: expr, $ty_ctx: expr; $($fn_name: ident).+ : | $($param_type: ident),* | => $ret_type: ident) => {
        $name_ctx
            .insert_fully_qualified_symbol(
                [$(stringify!($fn_name)),+].map(|s| s.to_string()).to_vec(),
                $ty_ctx.callable_type(CallKind::Function, $ret_type, [$($param_type),*].to_vec()),
            )
            .and_then(|_| -> Option<()> { unreachable!() });
    };
}

impl From<&crate::ast::ComplexPattern> for TypedASTComplexPattern {
    fn from(pat: &crate::ast::ComplexPattern) -> Self {
        use crate::ast::*;
        match pat {
            ComplexPattern::Ctor(CtorPattern { name, inner }) => TypedASTComplexPattern::Ctor {
                name: name.clone(),
                inner: inner.iter().map(|cx_pat| cx_pat.into()).collect(),
            },
            ComplexPattern::Tuple(vec) => TypedASTComplexPattern::Tuple {
                fields: vec.iter().map(|cx| cx.into()).collect(),
            },
            ComplexPattern::Wildcard => TypedASTComplexPattern::Wildcard,
            ComplexPattern::Literal(lit) => TypedASTComplexPattern::Literal(lit.clone()),
        }
    }
}

impl TypedAST {
    fn resolve_type_with_at(&mut self, ast_type: &crate::ast::Type) -> TypeRef {
        let type_ref = self.resolve_type(None, ast_type, false);
        self.ty_ctx.reference_type(type_ref)
    }

    fn resolve_type(
        &mut self,
        name: Option<&str>,
        ast_type: &crate::ast::Type,
        allow_opaque: bool,
    ) -> TypeRef {
        match ast_type {
            crate::ast::Type::Arrow(_, _) => unimplemented!(),
            crate::ast::Type::Array(ty) => {
                let elem_ty = self.resolve_type(None, ty, allow_opaque);
                self.ty_ctx.array_type(elem_ty)
            }
            crate::ast::Type::Tuple(tuple) => {
                let mut fields = vec![];
                for ty in tuple {
                    let field_ty = self.resolve_type(None, ty, allow_opaque);
                    fields.push(field_ty);
                }

                self.ty_ctx.tuple_type(fields)
            }

            crate::ast::Type::Enum(e) => {
                let mut ctors = vec![];

                for crate::ast::ConstructorType { name, inner } in e {
                    let tys = inner
                        .iter()
                        .map(|ty| self.resolve_type(None, ty, allow_opaque))
                        .collect();
                    ctors.push((name.clone(), tys));
                }

                self.ty_ctx.enum_type(
                    ctors,
                    name.expect("enum type should has a name").to_string(),
                )
            }

            crate::ast::Type::Unit => self.ty_ctx.singleton_type(Primitive::Unit),
            crate::ast::Type::Named(s) => {
                if let Some(type_ref) = self.ty_ctx.get_type_ref_by_name(s) {
                    type_ref
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
            let type_ref = self.resolve_type(Some(name), con_list, true);
            self.ty_ctx.associate_name_and_ref(name, type_ref)
        }
    }

    fn resolve_import(&mut self, module: &crate::ast::Module) {
        let imports: Vec<_> = module
            .imports
            .iter()
            .map(|ref_path| ref_path.items.as_slice())
            .collect();
        self.name_ctx.resolve_import(imports.as_slice())
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
        let typed_lhs = self.check_type_of_expr(&stmt.lhs);
        let typed_rhs = self.check_type_of_expr(&stmt.rhs);

        if !self.ty_ctx.is_type_compatible(typed_rhs.typ, typed_rhs.typ) {
            panic!("inconsistent type when assigning");
        }

        TypedAsgnStmt {
            lhs: typed_lhs,
            rhs: typed_rhs,
        }
    }

    fn check_type_of_let(&mut self, stmt: &crate::ast::LetStmt) -> TypedLetStmt {
        let crate::ast::LetStmt {
            var_name,
            typ,
            expr,
        } = stmt;

        let type_ref = self.resolve_type(None, typ, false);
        let typed_expr = self.check_type_of_expr(expr);
        if !self.ty_ctx.is_type_compatible(type_ref, typed_expr.typ) {
            panic!("initializer of variable {} has incorrect type", var_name);
        }

        if var_name != "_" {
            self.name_ctx
                .insert_symbol(var_name.clone(), type_ref)
                .and_then(|_| -> Option<()> { panic!("duplicate definition {}", var_name) });
        }

        TypedLetStmt {
            var_name: var_name.to_string(),
            var_type: type_ref,
            expr: typed_expr,
        }
    }

    fn check_type_of_argument(&mut self, arg: &crate::ast::Argument) -> TypedArgument {
        match arg {
            crate::ast::Argument::Expr(e) => TypedArgument::Expr(self.check_type_of_expr(e)),
            crate::ast::Argument::AtVar(_) => {
                unimplemented!("not available")
                /*
                let typ = self
                    .name_ctx
                    .find_symbol(&[name.clone()])
                    .unwrap_or_else(|| panic!("variable undefined: {}", name));

                TypedArgument::AtVar(name.to_string(), typ)
                */
            }
        }
    }

    fn check_type_of_call(&mut self, call: &crate::ast::CallExpr) -> TypedExpr {
        let crate::ast::CallExpr { gen: _, args, func } = call;

        let TypedExpr { typ, expr } = self.check_type_of_expr(func);

        let Type::Callable {
            ret_type,
            parameters,
            kind,
        } = self.ty_ctx.get_type_by_ref(typ) else {
            panic!("try to call a non-callable entity");
        };

        let args: Vec<_> = args
            .iter()
            .map(|arg| self.check_type_of_argument(arg))
            .collect();

        if parameters.len() != args.len() {
            panic!(
                "wrong number of arguments: expect {} but given {}",
                parameters.len(),
                args.len()
            );
        }

        match kind {
            CallKind::Constructor => {
                for (idx, (&typ, typed_arg)) in parameters.iter().zip(args.iter()).enumerate() {
                    match typed_arg {
                        TypedArgument::Expr(e) => {
                            if !self.ty_ctx.is_type_compatible(typ, e.typ) {
                                panic!("argument {} type incorrect", idx);
                            }
                        }
                        TypedArgument::AtVar(_, _) => {
                            panic!("at expression was not allowed in constructor")
                        }
                    }
                }

                let path = match expr.as_ref() {
                    ExprEnum::Path {
                        path,
                        is_free_variable: _,
                    } => path,
                    _ => panic!("not a path in a constructor expression"),
                };

                assert!(path.len() == 1);

                TypedExpr {
                    expr: Box::new(ExprEnum::CtorCall {
                        args,
                        name: path[0].clone(),
                    }),
                    typ: ret_type,
                }
            }
            CallKind::Function | CallKind::ClosureValue => {
                for (idx, (&typ, typed_arg)) in parameters.iter().zip(args.iter()).enumerate() {
                    match typed_arg {
                        TypedArgument::Expr(e) => {
                            if !self.ty_ctx.is_type_compatible(typ, e.typ) {
                                panic!("argument {} type incorrect", idx);
                            }
                        }
                        TypedArgument::AtVar(_, _) => {
                            unimplemented!("not available");
                            /*
                            if !self.ty_ctx.is_type_compatible(typ, *atvar_typ) {
                                panic!("argument {} type incorrect", idx);
                            }
                            */
                        }
                    }
                }

                if kind == CallKind::ClosureValue {
                    TypedExpr {
                        expr: Box::new(ExprEnum::ClosureCall {
                            expr: TypedExpr { typ, expr },
                            args,
                        }),
                        typ: ret_type,
                    }
                } else {
                    let path = match expr.as_ref() {
                        ExprEnum::Path {
                            path,
                            is_free_variable: _,
                        } => path,
                        _ => panic!("not a path in a function call expression"),
                    };

                    TypedExpr {
                        expr: Box::new(ExprEnum::Call {
                            path: path.clone(),
                            args,
                        }),
                        typ: ret_type,
                    }
                }
            }
        }
    }

    fn convert_pattern_struct(
        &self,
        pattern: &crate::ast::ComplexPattern,
    ) -> TypedASTComplexPattern {
        use TypedASTComplexPattern::*;
        match pattern {
            crate::ast::ComplexPattern::Ctor(crate::ast::CtorPattern { name, inner }) => {
                if self.name_ctx.find_ctor(name).is_some() {
                    Ctor {
                        name: name.clone(),
                        inner: inner
                            .iter()
                            .map(|x| self.convert_pattern_struct(x))
                            .collect(),
                    }
                } else if !inner.is_empty() {
                    panic!("invalid constructor for match arm: constructor doesn't exist")
                } else {
                    Variable(name.clone())
                }
            }
            crate::ast::ComplexPattern::Tuple(x) => Tuple {
                fields: x.iter().map(|x| self.convert_pattern_struct(x)).collect(),
            },
            crate::ast::ComplexPattern::Wildcard => Wildcard,
            crate::ast::ComplexPattern::Literal(x) => Literal(x.clone()),
        }
    }

    fn insert_pattern_symbol_binding(
        &mut self,
        matched_type: TypeRef,
        pattern: &TypedASTComplexPattern,
    ) {
        use TypedASTComplexPattern::*;
        match pattern {
            Ctor { name, inner } => {
                let Some(typ) = self.name_ctx.find_ctor(name) else { unreachable!("{}", name)};
                let ctor_type = self.ty_ctx.get_type_by_ref(typ);
                let Type::Callable {
                    kind,
                    ret_type,
                    parameters,
                } = ctor_type else {
                    panic!("constructor type is not callable")
                };
                if !self.ty_ctx.is_type_compatible(ret_type, matched_type) {
                    panic!("invalid constructor for match arm: constructor belongs to another type")
                }
                assert_eq!(kind, CallKind::Constructor);
                if parameters.len() != inner.len() {
                    panic!(
                        "requires {} parameters for constructor but got {}",
                        parameters.len(),
                        inner.len()
                    );
                }

                for (&param, pattern) in parameters.iter().zip(inner.iter()) {
                    self.insert_pattern_symbol_binding(param, pattern);
                }
            }
            Tuple { fields: vec } => {
                let tuple_type = self.ty_ctx.get_type_by_ref(matched_type);
                let Type::Tuple { fields } = tuple_type else {
                    panic!("invalid tuple pattern")
                };
                if fields.len() != vec.len() {
                    panic!("requires {} fields but got {}", fields.len(), vec.len());
                }
                for (&field, pattern) in fields.iter().zip(vec.iter()) {
                    self.insert_pattern_symbol_binding(field, pattern);
                }
            }
            Wildcard => {}
            Literal(lit) => {
                let typ = self.check_type_of_literal(lit).typ;
                if !self.ty_ctx.is_type_compatible(typ, matched_type) {
                    panic!("invalid literal for match arm: type is not compatible")
                }
            }
            Variable(name) => {
                // regard this "ctor" as variable binding
                self.name_ctx
                    .insert_symbol(name.to_string(), matched_type)
                    .and_then(|_| -> Option<()> { panic!("{} has existed", name) });
            }
        }
    }

    // check expression in a match arm context
    fn check_type_of_expr_with_pattern_binding(
        &mut self,
        pattern: &crate::ast::ComplexPattern,
        expr: &crate::ast::Expr,
        matched_type: TypeRef,
    ) -> (TypedASTComplexPattern, TypedExpr) {
        self.name_ctx.entry_scope();

        let new_complex_pattern = self.convert_pattern_struct(pattern);
        self.insert_pattern_symbol_binding(matched_type, &new_complex_pattern);
        let typed_expr = self.check_type_of_expr(expr);

        self.name_ctx.exit_scope();

        (new_complex_pattern, typed_expr)
    }

    fn check_type_of_match(&mut self, expr: &crate::ast::MatchExpr) -> TypedExpr {
        let crate::ast::MatchExpr { e, arms } = expr;
        let match_expr = self.check_type_of_expr(e);

        // empty match
        if arms.is_empty() {
            panic!("empty match is not allowed")
        }

        let mut typed_arms = vec![];
        for (pat, expr) in arms {
            let typed_arm = self.check_type_of_expr_with_pattern_binding(pat, expr, match_expr.typ);
            typed_arms.push(typed_arm);
        }

        let result_expr_type = typed_arms.first().unwrap().1.typ;

        if !typed_arms
            .iter()
            .all(|(_, expr)| self.ty_ctx.is_type_eq(expr.typ, result_expr_type))
        {
            panic!("match arm returns incompatible types")
        }

        TypedExpr {
            expr: Box::new(ExprEnum::Match {
                expr: match_expr,
                arms: typed_arms,
            }),
            typ: result_expr_type,
        }
    }

    fn check_type_of_literal(&mut self, lit: &crate::ast::Literal) -> TypedExpr {
        use crate::ast::Literal::*;
        let typ = match lit {
            Float(_) => self.ty_ctx.singleton_type(Primitive::Float64),
            Int(_) => self.ty_ctx.singleton_type(Primitive::Int32),
            Str(_) => self.ty_ctx.singleton_type(Primitive::Str),
            Bool(_) => self.ty_ctx.singleton_type(Primitive::Bool),
            Unit => self.ty_ctx.singleton_type(Primitive::Unit),
        };

        TypedExpr {
            typ,
            expr: Box::new(ExprEnum::Lit(lit.clone())),
        }
    }

    fn check_type_of_expr(&mut self, expr: &crate::ast::Expr) -> TypedExpr {
        match expr {
            crate::ast::Expr::Bracket(x) => {
                let TypedBracketBody {
                    stmts,
                    ret_expr,
                    typ,
                } = self.check_type_of_bracket_body(x);

                TypedExpr {
                    typ,
                    expr: Box::new(ExprEnum::Bracket { stmts, ret_expr }),
                }
            }
            crate::ast::Expr::Call(x) => self.check_type_of_call(x),
            crate::ast::Expr::BinOp(x) => self.check_type_of_binary(x),
            crate::ast::Expr::Match(x) => self.check_type_of_match(x),
            crate::ast::Expr::Lit(x) => self.check_type_of_literal(x),
            crate::ast::Expr::Closure(x) => self.check_type_of_closure(x),
            crate::ast::Expr::If(x) => self.check_type_of_if(x),
            crate::ast::Expr::UnaryOp(x) => self.check_type_of_unary(x),
            crate::ast::Expr::Subscript(x) => self.check_type_of_subscript(x),
            crate::ast::Expr::Tuple(x) => self.check_type_of_tuple(x),
            crate::ast::Expr::Path(x) => self.check_type_of_path(x),
        }
    }

    fn check_type_of_if(&mut self, expr: &crate::ast::IfExpr) -> TypedExpr {
        let crate::ast::IfExpr {
            condition,
            t_branch,
            f_branch,
        } = expr;
        let cond_expr = self.check_type_of_expr(condition);
        let then_expr = self.check_type_of_expr(t_branch);
        let or_expr = f_branch.as_ref().map(|br| self.check_type_of_expr(br));

        if !self.ty_ctx.is_boolean_testable_type(cond_expr.typ) {
            panic!("if expression has wrong type of condition");
        }

        if let Some(or_expr) = &or_expr {
            if !self.ty_ctx.is_type_eq(or_expr.typ, then_expr.typ) {
                panic!("if expression has inconsistent type of true and false branches");
            }
        } else if !self
            .ty_ctx
            .is_type_eq(self.ty_ctx.singleton_type(Primitive::Unit), then_expr.typ)
        {
            panic!("if expression without false branch must be unit type");
        }

        let typ = then_expr.typ;
        TypedExpr {
            expr: Box::new(ExprEnum::If {
                condition: cond_expr,
                then: then_expr,
                or: or_expr,
            }),
            typ,
        }
    }

    fn check_type_of_closure(&mut self, expr: &crate::ast::ClosureExpr) -> TypedExpr {
        let crate::ast::ClosureExpr {
            param_list,
            ret_type,
            body,
        } = expr;

        let ret_type = self.resolve_type(None, ret_type, false);
        let params_type: Vec<_> = param_list
            .iter()
            .map(
                |crate::ast::NameTypeBind {
                     with_at,
                     var_name: _,
                     typ,
                 }| {
                    if !*with_at {
                        self.resolve_type(None, typ, false)
                    } else {
                        self.resolve_type_with_at(typ)
                    }
                },
            )
            .collect();

        let params_vec: Vec<TypedBind> = param_list
            .iter()
            .zip(params_type.iter())
            .map(
                |(
                    crate::ast::NameTypeBind {
                        with_at,
                        var_name,
                        typ: _,
                    },
                    &typ,
                )| TypedBind {
                    with_at: *with_at,
                    var_name: var_name.clone(),
                    typ,
                },
            )
            .collect();

        let fn_ty = self
            .ty_ctx
            .callable_type(CallKind::Function, ret_type, params_type.clone());

        let inner_level = self.name_ctx.entry_scope();
        self.delimiter.push(inner_level);
        for (tp, var_name) in params_type.iter().zip(param_list.iter().map(
            |crate::ast::NameTypeBind {
                 with_at: _,
                 var_name,
                 typ: _,
             }| var_name,
        )) {
            self.name_ctx
                .insert_symbol(var_name.to_string(), *tp)
                .and_then(|_| -> Option<()> { panic!("parameter redefined") });
        }

        let body = self.check_type_of_expr(body);
        if !self.ty_ctx.is_type_compatible(body.typ, ret_type) {
            panic!("return type inconsistent of lambda expression");
        }

        self.name_ctx.exit_scope();
        self.delimiter.pop();

        TypedExpr {
            expr: Box::new(ExprEnum::Closure {
                param_list: params_vec,
                ret_type,
                body,
            }),
            typ: fn_ty,
        }
    }

    fn check_type_of_unary(&mut self, expr: &crate::ast::UnaryOpExpr) -> TypedExpr {
        let crate::ast::UnaryOpExpr { op, expr } = expr;
        let expr = self.check_type_of_expr(expr);

        use crate::ast::UnaryOp::*;
        if !match op {
            Not => self.ty_ctx.is_boolean_testable_type(expr.typ),
            Positive | Negative => self.ty_ctx.is_arithmetic_type(expr.typ),
        } {
            panic!("not compatible types for unary operator {:?}", op)
        }

        let ret_typ = match op {
            Not => self.ty_ctx.singleton_type(Primitive::Bool),
            Positive | Negative => expr.typ,
        };

        TypedExpr {
            expr: Box::new(ExprEnum::UnaryOp { expr, op: *op }),
            typ: ret_typ,
        }
    }

    fn check_type_of_subscript(&mut self, expr: &crate::ast::SubscriptExpr) -> TypedExpr {
        let crate::ast::SubscriptExpr { arr, index } = expr;
        let arr = self.check_type_of_expr(arr);
        let index = self.check_type_of_expr(index);

        if !self.ty_ctx.is_array_type(arr.typ) {
            panic!("invalid subscript operation on non-array type")
        }

        let array_type = &self.ty_ctx.get_type_by_ref(arr.typ);
        let elem_type = match array_type {
            Type::Array(elem) => *elem,
            _ => panic!("not a array type"),
        };

        if !self.ty_ctx.is_index_type(index.typ) {
            panic!("invalid type of the index value")
        }

        TypedExpr {
            expr: Box::new(ExprEnum::Subscript { arr, index }),
            typ: elem_type,
        }
    }

    fn check_type_of_tuple(&mut self, expr: &[crate::ast::Expr]) -> TypedExpr {
        let typed_expr: Vec<_> = expr
            .iter()
            .map(|expr| self.check_type_of_expr(expr))
            .collect();
        let fields_type: Vec<_> = typed_expr.iter().map(|expr| expr.typ).collect();
        let tuple_type = self.ty_ctx.tuple_type(fields_type);

        TypedExpr {
            expr: Box::new(ExprEnum::Tuple {
                elements: typed_expr,
            }),
            typ: tuple_type,
        }
    }

    fn check_type_of_path(&mut self, expr: &crate::ast::RefPath) -> TypedExpr {
        let crate::ast::RefPath { items } = expr;
        let (level, typ) = self.name_ctx.find_symbol_and_level(items);
        let typ = typ.unwrap_or_else(|| panic!("unable to find symbol {}", items.join(".")));

        // convert ctor with 0 parameters from path expr to ctor expr

        if let Type::Callable {
            kind: CallKind::Constructor,
            ret_type,
            parameters,
        } = self.ty_ctx.get_type_by_ref(typ)
        {
            if parameters.is_empty() {
                return TypedExpr {
                    expr: Box::new(ExprEnum::CtorCall {
                        name: items[0].clone(),
                        args: vec![],
                    }),
                    typ: ret_type,
                };
            }
        }

        let is_free_variable = level < *self.delimiter.last().unwrap();
        TypedExpr {
            expr: Box::new(ExprEnum::Path {
                path: items.clone(),
                is_free_variable,
            }),
            typ,
        }
    }

    fn determine_promoted_type(&self, t1: TypeRef, t2: TypeRef) -> TypeRef {
        match (
            self.ty_ctx
                .is_type_eq(t1, self.ty_ctx.singleton_type(Primitive::Float64)),
            self.ty_ctx
                .is_type_eq(t1, self.ty_ctx.singleton_type(Primitive::Int32)),
            self.ty_ctx
                .is_type_eq(t2, self.ty_ctx.singleton_type(Primitive::Float64)),
            self.ty_ctx
                .is_type_eq(t2, self.ty_ctx.singleton_type(Primitive::Int32)),
        ) {
            (true, _, _, _) | (_, _, true, _) => self.ty_ctx.singleton_type(Primitive::Float64),
            (_, true, _, true) => self.ty_ctx.singleton_type(Primitive::Int32),
            _ => panic!("unable to determine promote type"),
        }
    }

    fn check_type_of_binary(&mut self, expr: &crate::ast::BinOpExpr) -> TypedExpr {
        let crate::ast::BinOpExpr { lhs, rhs, op } = expr;
        let left = self.check_type_of_expr(lhs);
        let right = self.check_type_of_expr(rhs);

        use crate::ast::BinOp::*;
        if !match op {
            Or | And => {
                self.ty_ctx.is_boolean_testable_type(left.typ)
                    && self.ty_ctx.is_boolean_testable_type(right.typ)
                    && self.ty_ctx.is_type_compatible(left.typ, right.typ)
            }
            Eq | Ne => {
                self.ty_ctx.is_partially_equal_type(left.typ)
                    && self.ty_ctx.is_partially_equal_type(right.typ)
                    && self.ty_ctx.is_type_compatible(left.typ, right.typ)
            }
            Le | Ge | Lt | Gt => {
                self.ty_ctx.is_partially_ordered_type(left.typ)
                    && self.ty_ctx.is_partially_ordered_type(right.typ)
                    && self.ty_ctx.is_type_compatible(left.typ, right.typ)
            }
            Plus | Sub | Mul | Div | Mod => {
                self.ty_ctx.is_arithmetic_type(left.typ)
                    && self.ty_ctx.is_arithmetic_type(right.typ)
                    && self.ty_ctx.is_type_compatible(left.typ, right.typ)
            }
        } {
            panic!("not compatible types for binary operator {:?}", op)
        }

        let ret_typ = match op {
            Or | And => self.ty_ctx.singleton_type(Primitive::Bool),
            Eq | Ne => self.ty_ctx.singleton_type(Primitive::Bool),
            Le | Ge | Lt | Gt => self.ty_ctx.singleton_type(Primitive::Bool),
            Plus | Sub | Mul | Div | Mod => self.determine_promoted_type(left.typ, right.typ),
        };

        TypedExpr {
            expr: Box::new(ExprEnum::BinOp {
                lhs: left,
                rhs: right,
                op: *op,
            }),
            typ: ret_typ,
        }
    }

    fn check_type_of_while(&mut self, stmt: &crate::ast::WhileStmt) -> TypedWhileStmt {
        let crate::ast::WhileStmt { condition, body } = stmt;
        let cond_expr = self.check_type_of_expr(condition);

        if !self.ty_ctx.is_boolean_testable_type(cond_expr.typ) {
            panic!("while expression has wrong type of condition");
        }

        let body = self.check_type_of_bracket_body(body);

        TypedWhileStmt {
            condition: cond_expr,
            body: Box::new(body),
        }
    }

    fn check_type_of_for(&mut self, stmt: &crate::ast::ForStmt) -> TypedForStmt {
        let crate::ast::ForStmt {
            var_name,
            range_l,
            range_r,
            body,
        } = stmt;

        let range_l = self.check_type_of_expr(range_l);
        let range_r = self.check_type_of_expr(range_r);

        if !self.ty_ctx.is_index_type(range_l.typ)
            || !self.ty_ctx.is_index_type(range_r.typ)
            || !self.ty_ctx.is_type_eq(range_l.typ, range_r.typ)
        {
            panic!("range is not index type")
        }

        self.name_ctx.entry_scope();

        if var_name != "_" {
            self.name_ctx
                .insert_symbol(var_name.clone(), range_l.typ)
                .and_then(|_| -> Option<()> { panic!("internal error") });
        }

        let body = self.check_type_of_bracket_body(body);

        self.name_ctx.exit_scope();

        TypedForStmt {
            var_name: var_name.clone(),
            range_l,
            range_r,
            body: Box::new(body),
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
            crate::ast::Stmt::While(stmt) => {
                TypedASTStmt::While(Box::new(self.check_type_of_while(stmt)))
            }
            crate::ast::Stmt::For(stmt) => {
                TypedASTStmt::For(Box::new(self.check_type_of_for(stmt)))
            }
            crate::ast::Stmt::Return => TypedASTStmt::Return,
            crate::ast::Stmt::Break => TypedASTStmt::Break,
            crate::ast::Stmt::Continue => TypedASTStmt::Continue,
        }
    }

    fn check_type_of_bracket_body(&mut self, body: &crate::ast::BracketBody) -> TypedBracketBody {
        self.name_ctx.entry_scope();

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
            || self.ty_ctx.singleton_type(Primitive::Unit),
            |expr| expr.typ,
        );

        self.name_ctx.exit_scope();

        TypedBracketBody {
            stmts: typed_stmts,
            ret_expr: typed_expr,
            typ,
        }
    }

    fn check_type_of_function_signature(&mut self, func: &crate::ast::FuncDef) {
        let ret_type = self.resolve_type(None, &func.ret_type, false);

        let params_type: Vec<_> = func
            .param_list
            .iter()
            .map(
                |crate::ast::NameTypeBind {
                     with_at,
                     var_name: _,
                     typ,
                 }| {
                    if !*with_at {
                        self.resolve_type(None, typ, false)
                    } else {
                        self.resolve_type_with_at(typ)
                    }
                },
            )
            .collect();

        let fn_type = self
            .ty_ctx
            .callable_type(CallKind::Function, ret_type, params_type);
        self.name_ctx
            .insert_symbol(func.name.clone(), fn_type)
            .and_then(|_| -> Option<()> { panic!("function {} redefined", func.name) });
    }

    fn check_type_of_function(&mut self, func: &crate::ast::FuncDef) {
        let name = func.name.to_string();

        let typ = self
            .name_ctx
            .find_symbol(&[name.clone()])
            .unwrap_or_else(|| panic!("unable to find {}", name));

        let typ = &self.ty_ctx.get_type_by_ref(typ);

        let Type::Callable {
            kind: _,
            ret_type,
            parameters,
        } = typ else {
            panic!("not a callable type: {}", name);
        };

        self.name_ctx.entry_scope();
        let mut param_vec = vec![];

        for (
            idx,
            crate::ast::NameTypeBind {
                with_at,
                var_name,
                typ: _,
            },
        ) in func.param_list.iter().enumerate()
        {
            let tp = parameters[idx];
            param_vec.push(TypedBind {
                with_at: *with_at,
                var_name: var_name.clone(),
                typ: tp,
            });

            if var_name != "_" {
                self.name_ctx
                    .insert_symbol(var_name.to_string(), tp)
                    .and_then(|_| -> Option<()> { panic!("parameter redefined") });
            }
        }

        let body = self.check_type_of_bracket_body(&func.body);
        if !self.ty_ctx.is_type_compatible(body.typ, *ret_type) {
            panic!("return type inconsistent: {}", func.name);
        }

        self.name_ctx.exit_scope();

        self.module.push(TypedFuncDef {
            name: func.name.to_string(),
            ret_type: *ret_type,
            body: Box::new(body),
            params: param_vec,
        });
    }

    fn entry_scope(&mut self) {
        self.name_ctx.entry_scope();
    }

    fn exit_scope(&mut self) {
        self.name_ctx.exit_scope();
    }

    fn create_library_function_signature(&mut self) {
        let unit = self.ty_ctx.singleton_type(Primitive::Unit);
        let object = self.ty_ctx.singleton_type(Primitive::Object);
        let string = self.ty_ctx.singleton_type(Primitive::Str);
        let arr_of_str = self.ty_ctx.array_type(string);

        declare_library_function!(self.name_ctx, self.ty_ctx; std.io.print: |object| => unit);
        declare_library_function!(self.name_ctx, self.ty_ctx; std.io.println: |object| => unit);
        declare_library_function!(self.name_ctx, self.ty_ctx; std.io.readline: || => string);
        declare_library_function!(self.name_ctx, self.ty_ctx; std.string.split: |string, string| => arr_of_str);
    }

    pub fn create_from_ast(module: &crate::ast::Module) -> Self {
        let mut typed_ast = TypedAST::default();

        typed_ast.name_ctx.ctor_env = Some(typed_ast.ty_ctx.get_ctor_map());
        typed_ast.delimiter.push(-1); // closest delimiter is at -1, which means a global level

        typed_ast.entry_scope();
        typed_ast.create_library_function_signature();
        typed_ast.resolve_import(module);

        // Resolve type means transforming types in AST
        // to types in TypeContext.

        // resolve type in **data definitions**, first pass,
        // may leave opaque named type
        typed_ast.resolve_all_type(module);

        // resolve type, second pass, replace previously opaque
        // named type [Right(name)] with type index [Left(type_ref)].
        typed_ast.ty_ctx.refine_all_type();

        typed_ast.check_type(module);
        typed_ast.exit_scope();

        typed_ast
    }
}

impl From<crate::ast::Module> for TypedAST {
    fn from(module: crate::ast::Module) -> Self {
        TypedAST::create_from_ast(&module)
    }
}

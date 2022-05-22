use pest::Parser;

#[derive(Parser)]
#[grammar = "frontend/grammar.pest"]
pub struct CaloParser;

use pest::iterators::Pair;

use crate::ast::*;

#[cfg(test)]
mod tests;

pub fn parse<'a>(s: &'a str) -> Module {
    let mut prs = CaloParser::parse(Rule::Module, s).unwrap();
    let p = prs.next().unwrap();
    let t = parse_module(p);
    t
}

fn parse_module<'i>(p: Pair<'i, Rule>) -> Module {
    assert_eq!(p.as_rule(), Rule::Module);

    let mut imports : Vec<RefPath> = Vec::new();
    let mut data_defs : Vec<DataDef> = Vec::new();
    let mut func_defs : Vec<FuncDef> = Vec::new();

    let mut it = p.into_inner();
    let imp = it.next().unwrap();
    for path in imp.into_inner() {
        imports.push(parse_path(path));
    }

    let deb = it.next().unwrap();
    for def in deb.into_inner() {
        match def.as_rule() {
            Rule::DataDefinition => data_defs.push(parse_data_definition(def)),
            Rule::FunctionDefinition => func_defs.push(parse_function_definition(def)),
            _ => unreachable!()
        }
    }

    Module { imports, data_defs, func_defs }
}

fn parse_path<'i>(p: Pair<'i, Rule>) -> RefPath {
    assert_eq!(p.as_rule(), Rule::Path);

    let items: Vec<String> = p.into_inner().map(|i| i.as_str().to_string()).collect();
    RefPath { items }
}

fn parse_data_definition<'i>(p: Pair<'i, Rule>) -> DataDef {
    assert_eq!(p.as_rule(), Rule::DataDefinition);

    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let con_list = Type::Enum(it.next().unwrap()
        .into_inner()
        .map(parse_constructor_type)
        .collect());
    DataDef { name, con_list }
}

fn parse_constructor_type<'i>(p: Pair<'i, Rule>) -> ConstructorType {
    assert_eq!(p.as_rule(), Rule::Constructor);

    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let inner = match it.next() {
        None => Vec::new(),
        Some(pr) => pr.into_inner().map(parse_type).collect()
    };
    ConstructorType { name, inner }
}

fn parse_type<'i>(p: Pair<'i, Rule>) -> Type {
    match p.as_rule() {
        Rule::Type => parse_type(p.into_inner().next().unwrap()),
        Rule::ArrowT => {
            let mut tps: Vec<Type> = p.into_inner().map(parse_type).collect();
            // right-associative, so process from right to left
            let mut tp = tps.pop().unwrap(); // must have
            while !tps.is_empty() {
                let t = tps.pop().unwrap();
                tp = Type::Arrow(Box::new(t), Box::new(tp));
            }
            tp
        },
        Rule::TupleT => {
            let mut it = p.into_inner();
            let fir = it.next().unwrap();
            match fir.as_rule() {
                Rule::Type => {
                    // p represents a tuple
                    let mut tps: Vec<Type> = vec![parse_type(fir)];
                    tps.extend(it.map(parse_type));
                    Type::Tuple(tps)
                },
                Rule::ArrayT => parse_type(fir),
                _ => unreachable!()
            }
        },
        Rule::ArrayT => {
            let fir = p.into_inner().next().unwrap();
            match fir.as_rule() {
                Rule::Type => {
                    let t = parse_type(fir);
                    Type::Array(Box::new(t))
                },
                Rule::HighT => parse_type(fir),
                _ => unreachable!()

            }
        },
        Rule::HighT => {
            let fir = get_first(p);
            parse_type(fir)
        },
        Rule::UnitT => Type::Unit,
        Rule::NamedT => {
            let fir = get_first(p);
            let s = fir.as_str().to_string();
            Type::Named(s)
        }
        _ => unreachable!()
    }
}

fn parse_function_definition<'i>(p: Pair<'i, Rule>) -> FuncDef {
    assert_eq!(p.as_rule(), Rule::FunctionDefinition);

    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let param_list = parse_parameter_list(it.next().unwrap());
    let ret_type = parse_type(it.next().unwrap());
    let body = Box::new(parse_bracket_expression(it.next().unwrap()));
    FuncDef { name, param_list, ret_type, body }
}

fn parse_parameter_list<'i>(p: Pair<'i, Rule>) -> Vec<NameTypeBind> {
    p.into_inner().map(parse_name_type_bind).collect()
}

fn parse_name_type_bind<'i>(p: Pair<'i, Rule>) -> NameTypeBind {
    let with_at : bool;
    match p.as_rule() {
        Rule::AtNameTypeBind => with_at = true,
        Rule::OrdNameTypeBind => with_at = false,
        _ => unreachable!()
    }
    let mut it = p.into_inner();
    let var_name = it.next().unwrap().as_str().to_string();
    let typ = parse_type(it.next().unwrap());
    NameTypeBind { with_at, var_name, typ }
}

fn parse_bracket_expression<'i>(p: Pair<'i, Rule>) -> BracketBody {
    assert_eq!(p.as_rule(), Rule::BracketExpression);
    parse_bracket_body(get_first(p))
}

fn parse_bracket_body<'i>(p: Pair<'i, Rule>) -> BracketBody {
    assert_eq!(p.as_rule(), Rule::BracketBody);

    let mut stmts: Vec<Stmt> = Vec::new();
    let mut ret_expr = None;
    for q in p.into_inner() {
        match q.as_rule() {
            Rule::Statement => stmts.push(parse_statement(q)),
            Rule::Expression => ret_expr = Some(Box::new(parse_expression(q))),
            _ => unreachable!()
        }
    }
    BracketBody { stmts, ret_expr }
}

fn parse_statement<'i>(p: Pair<'i, Rule>) -> Stmt {
    assert_eq!(p.as_rule(), Rule::Statement);
    parse_statement_body(get_first(p))
}

fn parse_statement_body<'i>(p: Pair<'i, Rule>) -> Stmt {
    assert_eq!(p.as_rule(), Rule::StatementBody);

    let p = get_first(p);
    match p.as_rule() {
        Rule::Let => {
            let mut it = p.into_inner();
            let var_name = it.next().unwrap().as_str().to_string();
            let typ = parse_type(it.next().unwrap());
            let expr = Box::new(parse_expression(it.next().unwrap()));
            Stmt::Let(Box::new(LetStmt { var_name, typ, expr }))
        }
        Rule::While => {
            let mut it = p.into_inner();
            let condition = Box::new(parse_expression(it.next().unwrap()));
            let body = Box::new(parse_bracket_expression(it.next().unwrap()));
            Stmt::While(Box::new(WhileStmt { condition, body }))
        }
        Rule::For => {
            let mut it = p.into_inner();
            let var_name = it.next().unwrap().as_str().to_string();
            let (range_l, range_r) = parse_for_range(it.next().unwrap());
            let body = Box::new(parse_bracket_expression(it.next().unwrap()));
            Stmt::For(Box::new(ForStmt { var_name, range_l, range_r, body }))
        }
        Rule::Return => Stmt::Return,
        Rule::Break => Stmt::Break,
        Rule::Continue => Stmt::Continue,
        Rule::Asgn => {
            let mut it = p.into_inner();
            let lexp = Box::new(parse_expression(it.next().unwrap()));
            let rexp = Box::new(parse_expression(it.next().unwrap()));
            Stmt::Asgn(Box::new(AsgnStmt { lhs: lexp, rhs: rexp }))
        }
        Rule::Expression => {
            let t = parse_expression(p);
            Stmt::Expr(Box::new(t))
        }
        _ => unreachable!()
    }
}

fn parse_for_range<'i>(p: Pair<'i, Rule>) -> (Box<Expr>, Box<Expr>) {
    assert_eq!(p.as_rule(), Rule::ForRange);
    let mut it = p.into_inner();
    let l = Box::new(parse_expression(it.next().unwrap()));
    let r = Box::new(parse_expression(it.next().unwrap()));
    (l, r)
}

fn parse_expression<'i>(p: Pair<'i, Rule>) -> Expr {
    match p.as_rule() {
        Rule::Expression => parse_expression(get_first(p)),
        Rule::Closure => {
            let mut it = p.into_inner();
            let fir = it.next().unwrap();
            match fir.as_rule() {
                Rule::ParameterList => {
                    let param_list = parse_parameter_list(fir);
                    let ret_type = Box::new(parse_type(it.next().unwrap()));
                    let body = Box::new(parse_expression(it.next().unwrap()));
                    Expr::Closure(ClosureExpr { param_list, ret_type, body })
                }
                Rule::ControlFlow => parse_expression(fir),
                _ => unreachable!()
            }
        }
        Rule::ControlFlow => parse_expression(get_first(p)),
        Rule::Match => {
            let mut it = p.into_inner();
            let e = Box::new(parse_expression(it.next().unwrap()));
            let arms: Vec<_> = it.next().unwrap().into_inner().map(parse_match_arm).collect();
            Expr::Match(MatchExpr { e, arms })
        }
        Rule::If => {
            let mut it = p.into_inner();
            let condition = Box::new(parse_expression(it.next().unwrap()));
            let t_branch = Box::new(parse_expression(it.next().unwrap()));
            let f_branch = it.next().map(|q| Box::new(parse_expression(q)));
            Expr::If(IfExpr { condition, t_branch, f_branch })
        }
        Rule::Or => {
            let mut it = p.into_inner();
            let mut fir = parse_expression(it.next().unwrap());
            while let Some(q) = it.next() {
                let sec = parse_expression(q);
                fir = Expr::BinOp(BinOpExpr {
                    lhs: Box::new(fir),
                    rhs: Box::new(sec),
                    op: BinOp::Or
                });
            }
            fir
        }
        Rule::And => {
            let mut it = p.into_inner();
            let mut fir = parse_expression(it.next().unwrap());
            while let Some(q) = it.next() {
                let sec = parse_expression(q);
                fir = Expr::BinOp(BinOpExpr {
                    lhs: Box::new(fir),
                    rhs: Box::new(sec),
                    op: BinOp::And
                });
            }
            fir
        }
        Rule::Not => parse_expression(get_first(p)),
        Rule::NotC => {
            let fir = parse_expression(get_first(p));
            Expr::UnaryOp(UnaryOpExpr {
                expr: Box::new(fir),
                op: UnaryOp::Not
            })
        }
        Rule::Compare => {
            let mut it = p.into_inner();
            let fir = parse_expression(it.next().unwrap());
            match it.next() {
                None => fir,
                Some(q) => {
                    let op = parse_bin_op(q);
                    let sec = parse_expression(it.next().unwrap());
                    Expr::BinOp(BinOpExpr {
                        lhs: Box::new(fir),
                        rhs: Box::new(sec),
                        op
                    })
                }
            }
        }
        Rule::Arith1 => {
            let mut it = p.into_inner();
            let mut fir = parse_expression(it.next().unwrap());
            while let Some(q) = it.next() {
                let op = parse_bin_op(q);
                let sec = parse_expression(it.next().unwrap());
                fir = Expr::BinOp(BinOpExpr {
                    lhs: Box::new(fir),
                    rhs: Box::new(sec),
                    op
                });
            }
            fir
        }
        Rule::Arith2 => {
            let mut it = p.into_inner();
            let mut fir = parse_expression(it.next().unwrap());
            while let Some(q) = it.next() {
                let op = parse_bin_op(q);
                let sec = parse_expression(it.next().unwrap());
                fir = Expr::BinOp(BinOpExpr {
                    lhs: Box::new(fir),
                    rhs: Box::new(sec),
                    op
                });
            }
            fir
        }
        Rule::Arith3 => {
            let mut it = p.into_inner();
            let fir = it.next().unwrap();
            match fir.as_rule() {
                Rule::Arith3Op => {
                    let op = parse_una_op(fir);
                    let x = parse_expression(it.next().unwrap());
                    Expr::UnaryOp(UnaryOpExpr {
                        expr: Box::new(x),
                        op
                    })
                }
                Rule::Subscript => parse_expression(fir),
                _ => unreachable!()
            }
        }
        Rule::Subscript => {
            let mut it = p.into_inner();
            let mut fir = parse_expression(it.next().unwrap());
            while let Some(q) = it.next() {
                let index = parse_expression(q);
                fir = Expr::Subscript(SubscriptExpr {
                    arr: Box::new(fir),
                    index: Box::new(index)
                });
            }
            fir
        }
        Rule::Call => {
            let mut it = p.into_inner();
            let mut fir = parse_expression(it.next().unwrap());
            while let Some(q) = it.next() {
                let mut jt = q.into_inner();
                let v = jt.next().unwrap();
                fir = match v.as_rule() {
                    Rule::GenericNotation => {
                        let gen = Some(parse_generic_notation(v));
                        let args = parse_call_arguments(jt.next().unwrap());
                        Expr::Call(CallExpr {
                            func: Box::new(fir),
                            gen,
                            args
                        })
                    }
                    Rule::CallArguments => {
                        let args = parse_call_arguments(v);
                        Expr::Call(CallExpr {
                            func: Box::new(fir),
                            gen: None,
                            args
                        })
                    }
                    _ => unreachable!()
                }
            }
            fir
        }
        Rule::Tuple => {
            let mut it = p.into_inner();
            let fir = it.next().unwrap();
            match fir.as_rule() {
                Rule::Expression => {
                    let mut tup = vec![parse_expression(fir)];
                    tup.extend(it.map(parse_expression));
                    Expr::Tuple(tup)
                }
                Rule::High => parse_expression(fir),
                _ => unreachable!()
            }
        }
        Rule::High => parse_expression(get_first(p)),
        Rule::BracketExpression => Expr::Bracket(parse_bracket_expression(p)),
        Rule::Literal => Expr::Lit(parse_literal(p)),
        Rule::Path => Expr::Path(parse_path(p)),
        Rule::UnitVal => Expr::Lit(Literal::Unit),
        _ => unreachable!()
    }
}

fn parse_match_arm<'i>(p: Pair<'i, Rule>) -> (ComplexPattern, Box<Expr>) {
    assert_eq!(p.as_rule(), Rule::MatchArm);

    let mut it = p.into_inner();
    let pattern = parse_pattern(it.next().unwrap());
    let expr = parse_expression(it.next().unwrap());
    (pattern, Box::new(expr))
}

fn parse_pattern<'i>(p: Pair<'i, Rule>) -> ComplexPattern {
    assert_eq!(p.as_rule(), Rule::Pattern);

    let p = get_first(p);
    match p.as_rule() {
        Rule::ConstructorPattern => {
            let mut it = p.into_inner();
            let con_name = it.next().unwrap().as_str().to_string();
            let inner = it.map(parse_pattern).collect();
            ComplexPattern::Ctor(CtorPattern { name: con_name, inner })
        }
        Rule::TuplePattern => {
            let inner = p.into_inner().map(parse_pattern).collect();
            ComplexPattern::Tuple(inner)
        }
        Rule::Wildcard => ComplexPattern::Wildcard,
        Rule::Literal => {
            let l = parse_literal(p);
            ComplexPattern::Literal(l)
        }
        _ => unreachable!()
    }
}

fn parse_literal<'i>(p: Pair<'i, Rule>) -> Literal {
    assert_eq!(p.as_rule(), Rule::Literal);

    let p = get_first(p);
    match p.as_rule() {
        Rule::float_lit => Literal::Float(p.as_str().parse().expect("parse float literal fail")),
        Rule::integer_lit => Literal::Int(p.as_str().parse().expect("parse integer literal fail")),
        Rule::string_lit => Literal::Str(get_first(p).as_str().to_string()),
        Rule::bool_lit => Literal::Bool(p.as_str().parse().unwrap()),
        _ => unreachable!()
    }
}

fn parse_bin_op<'i>(p: Pair<'i, Rule>) -> BinOp {
    use BinOp::*;

    match p.as_rule() {
        Rule::CompareOp => {
            match p.as_str() {
                "<=" => Le,
                ">=" => Ge,
                "==" => Eq,
                "!=" => Ne,
                "<" => Lt,
                ">" => Gt,
                _ => unreachable!()
            }
        }
        Rule::Arith1Op => {
            match p.as_str() {
                "+" => Plus,
                "-" => Sub,
                _ => unreachable!()
            }
        }
        Rule::Arith2Op => {
            match p.as_str() {
                "*" => Mul,
                "/" => Div,
                "%" => Mod,
                _ => unreachable!()
            }
        }
        _ => unreachable!()
    }
}

fn parse_una_op<'i>(p: Pair<'i, Rule>) -> UnaryOp {
    use UnaryOp::*;

    match p.as_rule() {
        Rule::Arith3Op => {
            match p.as_str() {
                "+" => Positive,
                "-" => Negative,
                _ => unreachable!()
            }
        }
        _ => unreachable!()
    }
}

fn parse_generic_notation<'i>(p: Pair<'i, Rule>) -> Type {
    assert_eq!(p.as_rule(), Rule::GenericNotation);

    parse_type(get_first(p))
}

fn parse_call_arguments<'i>(p: Pair<'i, Rule>) -> Vec<Argument> {
    assert_eq!(p.as_rule(), Rule::CallArguments);

    p.into_inner().map(parse_argument).collect()
}

fn parse_argument<'i>(p: Pair<'i, Rule>) -> Argument {
    assert_eq!(p.as_rule(), Rule::CallArgument);

    let p = get_first(p);
    match p.as_rule() {
        Rule::VariableName => Argument::AtVar(p.as_str().to_string()),
        Rule::Expression => Argument::Expr(parse_expression(p)),
        _ => unreachable!()
    }
}

fn get_first<'i>(p: Pair<'i, Rule>) -> Pair<'i, Rule> {
    p.into_inner().next().unwrap()
}
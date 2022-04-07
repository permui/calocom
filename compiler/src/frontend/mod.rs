use pest::Parser;

#[derive(Parser)]
#[grammar = "frontend/grammar.pest"]
pub struct CaloParser;

use pest::iterators::Pair;

use crate::ast::*;

pub fn parse<'a>(s: &'a str) -> Module {
    let mut prs = CaloParser::parse(Rule::Module, s).unwrap();
    let p = prs.next().unwrap();
    parse_module(p)
}

fn parse_module<'i>(p: Pair<'i, Rule>) -> Module {
    assert_eq!(p.as_rule(), Rule::Module);

    let mut imports : Vec<RefPath> = Vec::new();
    let mut data_defs : Vec<DataDef> = Vec::new();
    let mut func_defs : Vec<FuncDef> = Vec::new();

    let mut it = p.into_inner();
    let imp = it.next().unwrap();
    for path in imp.into_inner() {
        assert_eq!(path.as_rule(), Rule::Path);
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
    let inner = it.next().map(parse_type);
    ConstructorType { name, inner }
}

fn parse_type<'i>(p: Pair<'i, Rule>) -> Type {
    match p.as_rule() {
        Rule::Type => parse_type(p.into_inner().next().unwrap()),
        Rule::type0 => {
            let mut tps: Vec<Type> = p.into_inner().map(parse_type).collect();
            let mut tp = tps.pop().unwrap(); // must have
            while !tps.is_empty() {
                let t = tps.pop().unwrap();
                tp = Type::Arrow(Box::new(t), Box::new(tp));
            }
            tp
        },
        Rule::type1 => parse_type(p.into_inner().next().unwrap()),
        Rule::unit_type => Type::Unit,
        Rule::tuple_type => {
            let tps: Vec<Type> = p.into_inner().map(parse_type).collect();
            Type::Tuple(tps)
        },
        Rule::TypeName => Type::Named(p.as_str().to_string()),
        _ => unreachable!()
    }
}

fn parse_function_definition<'i>(p: Pair<'i, Rule>) -> FuncDef {
    assert_eq!(p.as_rule(), Rule::FunctionDefinition);
    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let param_list: Vec<NameTypeBind> = it.next().unwrap().into_inner().map(parse_name_type_bind).collect();
    let ret_type = parse_type(it.next().unwrap());
    let body = Box::new(parse_bracket_expression(it.next().unwrap()));
    FuncDef { name, param_list, ret_type, body }
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
    let p = p.into_inner().next().unwrap();
    match p.as_rule() {
        Rule::StatementBodyLet => {
            let mut it = p.into_inner();
            let var_name = it.next().unwrap().as_str().to_string();
            let typ = parse_type(it.next().unwrap());
            let expr = Box::new(parse_expression(it.next().unwrap()));
            Stmt::Let(Box::new(LetStmt { var_name, typ, expr }))
        }
        Rule::StatementBodyAsgn => {
            let mut it = p.into_inner();
            let var_name = it.next().unwrap().as_str().to_string();
            let expr = parse_expression(it.next().unwrap());
            let expr = Box::new(expr);
            Stmt::Asgn(Box::new(AsgnStmt { var_name, expr }))
        }
        Rule::Expression => Stmt::Expr(Box::new(parse_expression(p))),
        _ => unreachable!()
    }
}

fn parse_expression<'i>(p: Pair<'i, Rule>) -> Expr {
    match p.as_rule() {
        Rule::Expression => parse_expression(p.into_inner().next().unwrap()),
        Rule::aexp | Rule::aexp1 => {
            let mut it = p.into_inner();
            let mut e = parse_expression(it.next().unwrap());
            loop {
                let op = it.next();
                if let None = op { break; }
                let op = parse_op(op.unwrap());
                let rhs = parse_expression(it.next().unwrap());
                e = Expr::ArithExpr(ArithExpr {
                    lhs: Box::new(e), rhs: Box::new(rhs), op: op
                });
            }
            e
        }
        Rule::aexp2 => parse_expression(get_first(p)),
        Rule::aexp3 => parse_expression(get_first(p)),
        Rule::MatchExpression => {
            let mut it = p.into_inner();
            let e = Box::new(parse_expression(it.next().unwrap()));
            let arms: Vec<(Pattern, Box<Expr>)> = it.next().unwrap()
                .into_inner()
                .map(parse_match_arm)
                .collect();
            Expr::MatchExpr(MatchExpr {
                e, arms
            })
        },
        Rule::BracketExpression => Expr::BraExpr(parse_bracket_expression(p)),
        Rule::CallExpression => {
            let mut it = p.into_inner();
            let path = parse_path(it.next().unwrap());
            let mut gen: Option<Type> = None;
            let mut tmp = it.next().unwrap();
            if let Rule::GenericNotation = tmp.as_rule() {
                gen = Some(parse_type(get_first(tmp)));
                tmp = it.next().unwrap();
            }
            let args: Vec<Argument> = tmp.into_inner()
                .map(parse_argument)
                .collect();
            Expr::CallExpr(CallExpr { path, gen, args })
        },
        Rule::Literal => Expr::Lit(parse_literal(p)),
        Rule::VariableName => Expr::Var(p.as_str().to_string()),
        _ => unreachable!()
    }
}

fn parse_match_arm<'i>(p: Pair<'i, Rule>) -> (Pattern, Box<Expr>) {
    let mut it = p.into_inner();
    let pattern = parse_pattern(it.next().unwrap());
    let expr = parse_expression(it.next().unwrap());
    (pattern, Box::new(expr))
}

fn parse_argument<'i>(p: Pair<'i, Rule>) -> Argument {
    assert_eq!(p.as_rule(), Rule::ArgumentExpression);
    let p = get_first(p);
    match p.as_rule() {
        Rule::AtArgument => Argument::AtVar(get_first(p).as_str().to_string()),
        Rule::Expression => Argument::Expr(parse_expression(p)),
        _ => unreachable!()
    }
}

fn parse_literal<'i>(p: Pair<'i, Rule>) -> Literal {
    let p = get_first(p);
    match p.as_rule() {
        Rule::integer_lit => Literal::Int(p.as_str().parse().expect("parse integer error")),
        Rule::string_lit => Literal::Str(get_first(p).as_str().to_string()),
        Rule::bool_lit => Literal::Bool(p.as_str().parse().unwrap()),
        _ => unreachable!()
    }
}

fn parse_pattern<'i>(p: Pair<'i, Rule>) -> Pattern {
    let mut it = p.into_inner();
    let tmp = it.next().unwrap();
    match tmp.as_rule() {
        Rule::Literal => Pattern::Lit(parse_literal(tmp)),
        Rule::ConstructorName => {
            let name = tmp.as_str().to_string();
            let inner = it.next().map(|q| q.as_str().to_string());
            Pattern::Con(ConstructorVar {
                name, inner
            })
        }
        _ => unreachable!()
    }
}

fn parse_op<'i>(p: Pair<'i, Rule>) -> BinOp {
    match p.as_rule() {
        Rule::op => match p.as_str() {
            "+" => BinOp::Plus,
            "-" => BinOp::Sub,
            _ => unreachable!()
        },
        Rule::op1 => match p.as_str() {
            "*" => BinOp::Mult,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,
            _ => unreachable!()
        },
        _ => unreachable!()
    }
}

fn get_first<'i>(p: Pair<'i, Rule>) -> Pair<'i, Rule> {
    p.into_inner().next().unwrap()
}
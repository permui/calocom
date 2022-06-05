use super::ast::*;
use super::frontend::parse;
use std::path::PathBuf;
#[allow(unused)]
use std::{fmt::DebugTuple, fs};

const HTML_PROVISION: &str =
    "<script src=\"https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js\"></script>
<script>
mermaid.initialize({startOnLoad:true, maxTextSize: 500000});
</script>
<style>
    .mermaid {}
</style>

<script src=\"https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js\"></script>
<script>
mermaid.initialize({startOnLoad:false});
</script>
<script>
function renderMermaid(){
    mermaid.init(undefined,document.querySelectorAll(\".mermaid\"));
}
$(function() {
    $(document).on('previewUpdated', function() {        
        renderMermaid();
    });
    renderMermaid();
});
</script>
";

pub fn generate_html(path: &PathBuf) -> Result<(), String> {
    let source = match fs::read_to_string(path) {
        Ok(res) => res,
        Err(info) => return Err(info.to_string()),
    };
    let m = parse(&source);
    println!("{}", HTML_PROVISION);
    println!(
        "<div class=\"mermaid\">\n%%{{init: {{'theme':'dark'}}}}%%\ngraph\n{}\n</div>\n",
        generate_imports(&m)
    );
    println!(
        "<div class=\"mermaid\">\n%%{{init: {{'theme':'dark'}}}}%%\ngraph\n{}\n</div>\n",
        generate_data_defs(&m)
    );
    println!(
        "<div class=\"mermaid\">\n%%{{init: {{'theme':'dark'}}}}%%\ngraph\n{}\n</div>\n",
        generate_func_defs(&m)
    );
    Ok(())
}

fn generate_imports(m: &Module) -> String {
    let mut ret = String::from("imports((Imports))\n");
    let imports = &m.imports;
    for (import_cnt, import) in imports.iter().enumerate() {
        let items = &import.items;
        let full_path: String = items.join(".");
        let cnt_string = import_cnt.to_string();
        let cnt_str = cnt_string.as_str();
        ret.push_str(
            format!(
                "imports_{}_(({}))\nimports-->imports_{}_\n",
                cnt_str, full_path, cnt_str
            )
            .as_str(),
        );
    }
    ret
}

fn generate_data_defs(m: &Module) -> String {
    let mut ret = String::from("data_defs((Data Definitions))\n");
    let data_defs = &m.data_defs;
    for (data_def_cnt, data_def) in data_defs.iter().enumerate() {
        ret.push_str(generate_data_def(data_def, data_def_cnt.to_string()).as_str());
        ret.push_str(
            format!(
                "data_defs-->data_def__{}_\n",
                data_def_cnt.to_string().as_str()
            )
            .as_str(),
        );
    }
    ret
}

fn generate_data_def(m: &DataDef, prefix: String) -> String {
    let mut ret = format!("data_def__{}_((Data Definition))\n", prefix);
    let name = &m.name;
    let con_list = &m.con_list;
    ret.push_str(
        format!(
            "data__{}_((data))\ndata_def__{}_-->data__{}_\n",
            prefix, prefix, prefix
        )
        .as_str(),
    );
    ret.push_str(
        format!(
            "name__{}_(({}))\ndata_def__{}_-->name__{}_\n",
            prefix, name, prefix, prefix
        )
        .as_str(),
    );
    // ret.push_str(format!("data_eq__{}_((=))\ndata_def__{}_-->data_eq__{}_\n", prefix, prefix, prefix).as_str());
    ret.push_str(generate_type(con_list, prefix.clone()).as_str());
    ret.push_str(format!("data_def__{}_-->type__{}_\n", prefix, prefix).as_str());
    ret
}

fn generate_type(con_list: &Type, prefix: String) -> String {
    let mut ret = format!("type__{}_((Type))\n", prefix);
    let type_string = match con_list {
        Type::Arrow(first, second) => {
            let mut arrow_ret = format!("type_arrow__{}_((Arrow))\n", prefix);
            arrow_ret.push_str(generate_type(first, prefix.clone() + "_0_").as_str());
            arrow_ret.push_str(generate_type(second, prefix.clone() + "_1_").as_str());
            arrow_ret.push_str(
                format!("type_arrow__{}_-->type_arrow__{}__0_\n", prefix, prefix).as_str(),
            );
            arrow_ret.push_str(
                format!("type_arrow__{}_-->type_arrow__{}__1_\n", prefix, prefix).as_str(),
            );
            arrow_ret.push_str(format!("type__{}_-->type_arrow__{}_\n", prefix, prefix).as_str());
            arrow_ret
        }
        Type::Enum(first) => {
            let mut enum_ret = format!("type_enum__{}_((Enum))\n", prefix);
            enum_ret.push_str(generate_vec_constructor_type(first, prefix.clone() + "_").as_str());
            enum_ret.push_str(
                format!(
                    "type_enum__{}_-->type_vec_constructor_type__{}_\n",
                    prefix,
                    prefix.clone() + "_"
                )
                .as_str(),
            );
            enum_ret.push_str(format!("type__{}_-->type_enum__{}_\n", prefix, prefix).as_str());
            enum_ret
        }
        Type::Named(first) => {
            let mut named_ret = format!("type_named__{}_((Named))\n", prefix);
            named_ret.push_str(
                format!(
                    "type_named_string__{}_(({}))\ntype_named__{}_-->type_named_string__{}_\n",
                    prefix, first, prefix, prefix
                )
                .as_str(),
            );
            named_ret.push_str(format!("type__{}_-->type_named__{}_\n", prefix, prefix).as_str());
            named_ret
        }
        Type::Tuple(first) => {
            let mut tuple_ret = format!("type_tuple__{}_((Tuple))\n", prefix);
            for (tuple_ret_cnt, i) in first.iter().enumerate() {
                tuple_ret.push_str(
                    generate_type(i, prefix.clone() + tuple_ret_cnt.to_string().as_str()).as_str(),
                );
                tuple_ret.push_str(
                    format!(
                        "type_tuple__{}_--> type__{}_\n",
                        prefix,
                        prefix.clone() + tuple_ret_cnt.to_string().as_str()
                    )
                    .as_str(),
                );
            }
            tuple_ret.push_str(format!("type__{}_-->type_tuple__{}_\n", prefix, prefix).as_str());
            tuple_ret
        }
        Type::Unit => {
            format!(
                "type_unit__{}_((Unit))\ntype__{}_-->type_unit__{}_\n",
                prefix, prefix, prefix
            )
        }
        Type::Array(ptr) => {
            let mut array_ret = format!("type_array__{}_((Array))\n", prefix);
            array_ret.push_str(&generate_type(ptr, prefix.clone() + "_in_array_box_"));
            array_ret.push_str(
                format!(
                    "type_array__{}_-->type__{}_\n",
                    prefix,
                    prefix.clone() + "_in_array_box_"
                )
                .as_str(),
            );
            array_ret.push_str(format!("type__{}_-->type_array__{}_\n", prefix, prefix).as_str());
            array_ret
        }
    };
    ret.push_str(type_string.as_str());
    ret
}

fn generate_vec_constructor_type(vector: &[ConstructorType], prefix: String) -> String {
    let mut ret = format!(
        "type_vec_constructor_type__{}_((VecConstructorType))\n",
        prefix
    );
    for (ret_cnt, i) in vector.iter().enumerate() {
        ret.push_str(
            generate_construct_type(i, prefix.clone() + ret_cnt.to_string().as_str()).as_str(),
        );
        ret.push_str(
            format!(
                "type_vec_constructor_type__{}_-->type_constructor_type__{}_\n",
                prefix,
                prefix.clone() + ret_cnt.to_string().as_str()
            )
            .as_str(),
        );
    }
    ret
}

fn generate_construct_type(constructor_type: &ConstructorType, prefix: String) -> String {
    let mut ret = format!("type_constructor_type__{}_((ConstructorType))\n", prefix);
    ret.push_str(
        format!(
            "type_constructor_type_name__{}_(({}))\n",
            prefix, constructor_type.name
        )
        .as_str(),
    );
    ret.push_str(
        format!(
            "type_constructor_type__{}_-->type_constructor_type_name__{}_\n",
            prefix, prefix
        )
        .as_str(),
    );
    // if let Some(ref ano_type) = constructor_type.inner {
    // 	ret.push_str(generate_type(ano_type, prefix.clone() + "_").as_str());
    // 	ret.push_str(format!("type_constructor_type_{}-->type_{}\n", prefix, prefix.clone() + "_").as_str());
    // }
    for (generate_cnt, i) in constructor_type.inner.iter().enumerate() {
        ret.push_str(
            generate_type(i, prefix.clone() + "__" + &generate_cnt.to_string() + "_").as_str(),
        );
        ret.push_str(
            format!(
                "type_constructor_type__{}_-->type__{}_\n",
                prefix,
                prefix.clone() + "__" + &generate_cnt.to_string() + "_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_func_defs(m: &Module) -> String {
    let mut ret = String::from("func_defs((Function Definitions))\n");
    for (ret_cnt, i) in m.func_defs.iter().enumerate() {
        ret.push_str(generate_func_def(i, ret_cnt.to_string()).as_str());
        ret.push_str(format!("func_defs-->func_def__{}_\n", ret_cnt).as_str());
    }
    ret
}

fn generate_func_def(func_def: &FuncDef, prefix: String) -> String {
    let mut ret = format!("func_def__{}_((Function Definition))\n", prefix);
    ret.push_str(
        format!(
            "func_def_name__{}_(({}))\nfunc_def__{}_-->func_def_name__{}_\n",
            prefix, func_def.name, prefix, prefix
        )
        .as_str(),
    );
    // ret.push_str(format!("func_def_left_param_paren__{}_((\"(\"))\nfunc_def__{}_-->func_def_left_param_paren__{}_\n", prefix, prefix, prefix).as_str());
    ret.push_str(generate_vec_name_type_bind(&func_def.param_list, prefix.clone()).as_str());
    ret.push_str(format!("func_def__{}_-->vec_name_type_bind__{}_\n", prefix, prefix).as_str());
    // ret.push_str(format!("func_def_right_param_paren__{}_((\")\"))\nfunc_def__{}_-->func_def_right_param_paren__{}_\n", prefix, prefix, prefix).as_str());
    ret.push_str(generate_type(&func_def.ret_type, prefix.clone() + "_in_func_def_").as_str());
    ret.push_str(
        format!(
            "func_def__{}_-->type__{}_\n",
            prefix,
            prefix.clone() + "_in_func_def_"
        )
        .as_str(),
    );
    ret.push_str(
        generate_bracket_body(&func_def.body, prefix.clone() + "_in_bracket_body_").as_str(),
    );
    ret.push_str(
        format!(
            "func_def__{}_-->bracket_body__{}_\n",
            prefix,
            prefix.clone() + "_in_bracket_body_"
        )
        .as_str(),
    );
    ret
}

fn generate_bracket_body(bracket_body: &BracketBody, prefix: String) -> String {
    let mut ret = format!("bracket_body__{}_((FuncBody))\n", prefix);
    ret.push_str(&generate_vec_stmt(&bracket_body.stmts, prefix.clone()));
    ret.push_str(format!("bracket_body__{}_-->vec_stmt__{}_\n", prefix, prefix).as_str());
    if let Some(ref ret_expr) = bracket_body.ret_expr {
        ret.push_str(&generate_expr(ret_expr, prefix.clone() + "_in_expr_"));
        ret.push_str(
            format!(
                "bracket_body__{}_-->expr__{}_\n",
                prefix,
                prefix.clone() + "_in_expr_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_closure_expr(closure_expr: &ClosureExpr, prefix: String) -> String {
    let mut ret = format!("closure_expr__{}_((Closure))\n", prefix);
    ret.push_str(&generate_vec_name_type_bind(
        &closure_expr.param_list,
        prefix.clone() + "_in_vec_type_named_from_closure_",
    ));
    ret.push_str(
        format!(
            "closure_expr__{}_-->vec_name_type_bind__{}_\n",
            prefix,
            prefix.clone() + "_in_vec_type_named_from_closure_"
        )
        .as_str(),
    );
    ret.push_str(&generate_type(
        &closure_expr.ret_type,
        prefix.clone() + "_ret_type_of_closure_",
    ));
    ret.push_str(
        format!(
            "closure_expr__{}_-->type__{}_\n",
            prefix,
            prefix.clone() + "_ret_type_of_closure_"
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &closure_expr.body,
        prefix.clone() + "_body_of_closure_",
    ));
    ret.push_str(
        format!(
            "closure_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_body_of_closure_"
        )
        .as_str(),
    );
    ret
}

fn generate_match_expr(match_expr: &MatchExpr, prefix: String) -> String {
    let mut ret = format!("match_expr__{}_((MatchExpr))\n", prefix);
    ret.push_str(&generate_expr(
        &match_expr.e,
        prefix.clone() + "_expr_from_match_condition_",
    ));
    ret.push_str(
        format!(
            "match_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_expr_from_match_condition_"
        )
        .as_str(),
    );
    for (cnt, i) in match_expr.arms.iter().enumerate() {
        ret.push_str(&generate_complex_pattern(
            &i.0,
            prefix.clone() + "_in_complex_from_match_" + cnt.to_string().as_str() + "_",
        ));
        ret.push_str(
            format!(
                "match_expr__{}_-->complex_pattern__{}_\n",
                prefix,
                prefix.clone() + "_in_complex_from_match_" + cnt.to_string().as_str() + "_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_complex_pattern(complex_pattern: &ComplexPattern, prefix: String) -> String {
    let mut ret = format!("complex_pattern__{}_((ComplexPatter))\n", prefix);
    match complex_pattern {
        ComplexPattern::Ctor(ctor_pattern) => {
            ret.push_str(&generate_ctor_pattern(
                ctor_pattern,
                prefix.clone() + "_ctor_from_complex_",
            ));
            ret.push_str(
                format!(
                    "complex_pattern__{}_-->ctor_pattern__{}_\n",
                    prefix,
                    prefix.clone() + "_ctor_from_complex_"
                )
                .as_str(),
            );
        }
        _ => {}
        // ComplexPattern::Tuple(_) => todo!(),
        // ComplexPattern::Wildcard => todo!(),
        // ComplexPattern::Literal(_) => todo!(),
    }
    ret
}

fn generate_ctor_pattern(ctor_pattern: &CtorPattern, prefix: String) -> String {
    let mut ret = format!("ctor_pattern__{}_((Ctor))", prefix);
    ret.push_str(
        format!(
            "ctor_pattern_name__{}_(({}))\nctor_pattern__{}_-->ctor_pattern_name__{}_\n",
            prefix, ctor_pattern.name, prefix, prefix
        )
        .as_str(),
    );
    for (cnt, i) in ctor_pattern.inner.iter().enumerate() {
        ret.push_str(&generate_complex_pattern(
            i,
            prefix.clone() + "_" + cnt.to_string().as_str() + "_item_in_inner_",
        ));
        ret.push_str(
            format!(
                "ctor_pattern__{}_-->complex_pattern__{}_\n",
                prefix,
                prefix.clone() + "_" + cnt.to_string().as_str() + "_item_in_inner_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_if_expr(if_expr: &IfExpr, prefix: String) -> String {
    let mut ret = format!("if_expr__{}_((IfExpr))\n", prefix);
    ret.push_str(&generate_expr(
        &if_expr.condition,
        prefix.clone() + "_in_condition_from_if_",
    ));
    ret.push_str(
        format!(
            "if_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_in_condition_from_if_"
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &if_expr.t_branch,
        prefix.clone() + "_in_t_branch_",
    ));
    ret.push_str(
        format!(
            "if_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_in_t_branch_"
        )
        .as_str(),
    );
    if let Some(ref f_branch) = if_expr.f_branch {
        ret.push_str(&generate_expr(f_branch, prefix.clone() + "_in_f_branch_"));
        ret.push_str(
            format!(
                "if_expr__{}_-->expr__{}_\n",
                prefix,
                prefix.clone() + "_in_f_branch_"
            )
            .as_str(),
        );
    };
    ret
}

fn generate_bin_op_expr(bin_op_expr: &BinOpExpr, prefix: String) -> String {
    let mut ret = format!("bin_op_expr__{}_((BinOpExpr))\n", prefix);
    ret.push_str(&generate_expr(
        &bin_op_expr.lhs,
        prefix.clone() + "_bin_op_lhs_",
    ));
    ret.push_str(
        format!(
            "bin_op_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_bin_op_lhs_"
        )
        .as_str(),
    );
    ret.push_str(
        format!(
            "bin_op_operator__{}_(({}))\nbin_op_expr__{}_-->bin_op_operator__{}_\n",
            prefix,
            match bin_op_expr.op {
                BinOp::Or => "Or",
                BinOp::And => "And",
                BinOp::Le => "LessOrEqual",
                BinOp::Ge => "GreaterOrEqual",
                BinOp::Eq => "Equal",
                BinOp::Ne => "NotEqual",
                BinOp::Lt => "LessThan",
                BinOp::Gt => "CreaterThan",
                BinOp::Plus => "Plus",
                BinOp::Sub => "Sub",
                BinOp::Mul => "Mul",
                BinOp::Div => "Div",
                BinOp::Mod => "Mod",
            },
            prefix,
            prefix
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &bin_op_expr.rhs,
        prefix.clone() + "_bin_op_rhs_",
    ));
    ret.push_str(
        format!(
            "bin_op_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_bin_op_rhs_"
        )
        .as_str(),
    );
    ret
}

fn generate_unary_op_expr(unary_op_expr: &UnaryOpExpr, prefix: String) -> String {
    let mut ret = format!("unary_op_expr__{}_((UnaryOpExpr))\n", prefix);
    ret.push_str(&generate_expr(
        &unary_op_expr.expr,
        prefix.clone() + "_expr_from_unary_",
    ));
    ret.push_str(
        format!(
            "unary_op_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_expr_from_unary_"
        )
        .as_str(),
    );
    ret.push_str(
        format!(
            "unary_op_expr_op__{}_(({}))\nunary_op_expr__{}_-->unary_op_expr_op__{}_\n",
            prefix,
            match unary_op_expr.op {
                UnaryOp::Not => "Not",
                UnaryOp::Positive => "Positive",
                UnaryOp::Negative => "Negative",
            },
            prefix,
            prefix
        )
        .as_str(),
    );
    ret
}

fn generate_subscript_expr(subscript_expr: &SubscriptExpr, prefix: String) -> String {
    let mut ret = format!("subscript_expr__{}_((Subscript))\n", prefix);
    ret.push_str(&generate_expr(
        &subscript_expr.arr,
        prefix.clone() + "_arr_from_subscript_",
    ));
    ret.push_str(
        format!(
            "subscript_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_arr_from_subscript_"
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &subscript_expr.index,
        prefix.clone() + "_index_from_subscript_",
    ));
    ret.push_str(
        format!(
            "subscript_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_index_from_subscript_"
        )
        .as_str(),
    );
    ret
}

fn generate_call_expr(call_expr: &CallExpr, prefix: String) -> String {
    let mut ret = format!("call_expr__{}_((Call))\n", prefix);
    ret.push_str(&generate_expr(&call_expr.func, prefix.clone() + "_func_"));
    ret.push_str(
        format!(
            "call_expr__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_func_"
        )
        .as_str(),
    );
    if let Some(gen_type) = &call_expr.gen {
        ret.push_str(&generate_type(gen_type, prefix.clone() + "_gen_"));
        ret.push_str(
            format!(
                "call_expr__{}_-->type__{}_\n",
                prefix,
                prefix.clone() + "_gen_"
            )
            .as_str(),
        );
    }
    for (cnt, i) in call_expr.args.iter().enumerate() {
        ret.push_str(&generate_argument(
            i,
            prefix.clone() + "_arg_" + cnt.to_string().as_str() + "_",
        ));
        ret.push_str(
            format!(
                "call_expr__{}_-->argument__{}_\n",
                prefix,
                prefix.clone() + "_arg_" + cnt.to_string().as_str() + "_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_argument(argument: &Argument, prefix: String) -> String {
    let mut ret = format!("argument__{}_((Argument))\n", prefix);
    match argument {
        Argument::Expr(expr) => {
            ret.push_str(&generate_expr(
                expr,
                prefix.clone() + "_expr_from_argument_",
            ));
            ret.push_str(
                format!(
                    "argument__{}_-->expr__{}_\n",
                    prefix,
                    prefix.clone() + "_expr_from_argument_"
                )
                .as_str(),
            );
        }
        Argument::AtVar(the_string) => {
            ret.push_str(
                format!(
                    "argument_at_var__{}_(({}))\nargument__{}_-->argument_at_var__{}_\n",
                    prefix, the_string, prefix, prefix
                )
                .as_str(),
            );
        }
    }
    ret
}

fn generate_tuple_expr(tuple_expr: &[Expr], prefix: String) -> String {
    let mut ret = format!("tuple__{}_((Tuple))\n", prefix);
    for (cnt, i) in tuple_expr.iter().enumerate() {
        ret.push_str(&generate_expr(
            i,
            prefix.clone() + "_tuple_" + cnt.to_string().as_str() + "_",
        ));
        ret.push_str(
            format!(
                "tuple__{}_-->expr__{}_\n",
                prefix,
                prefix.clone() + "_tuple_" + cnt.to_string().as_str() + "_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_literal(lit_expr: &Literal, prefix: String) -> String {
    let mut ret = format!("literal__{}_((Literal))\n", prefix);
    ret.push_str(
        match lit_expr {
            Literal::Float(fp) => format!(
                "literal_float__{}_(({}))\nliteral__{}_-->literal_float__{}_\n",
                prefix, fp, prefix, prefix
            ),
            Literal::Int(int) => format!(
                "literal_int__{}_(({}))\nliteral__{}_-->literal_int__{}_\n",
                prefix, int, prefix, prefix
            ),
            Literal::Str(_the_string) => format!(
                "literal_str_{}_(({}))\nliteral__{}_-->literal_str_{}_\n",
                prefix, "literal String", prefix, prefix
            ),
            Literal::Bool(the_bool) => format!(
                "literal_bool_{}_(({}))\nliteral__{}_-->literal_bool_{}_\n",
                prefix, the_bool, prefix, prefix
            ),
            Literal::Unit => format!(
                "literal_unit__{}_((Unit))\nliteral__{}_-->literal_unit__{}_",
                prefix, prefix, prefix
            ),
        }
        .as_str(),
    );
    ret
}

fn generate_expr(expr: &Expr, prefix: String) -> String {
    let mut ret = format!("expr__{}_((Expr))\n", prefix);
    match expr {
        Expr::Closure(closure_expr) => {
            ret.push_str(&generate_closure_expr(
                closure_expr,
                prefix.clone() + "_in_closure_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->closure_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_closure_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::Match(match_expr) => {
            ret.push_str(&generate_match_expr(
                match_expr,
                prefix.clone() + "_in_match_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->match_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_match_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::If(if_expr) => {
            ret.push_str(&generate_if_expr(
                if_expr,
                prefix.clone() + "_in_if_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->if_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_if_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::BinOp(bin_op_expr) => {
            ret.push_str(&generate_bin_op_expr(
                bin_op_expr,
                prefix.clone() + "_in_bin_op_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->bin_op_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_bin_op_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::UnaryOp(unary_op_expr) => {
            ret.push_str(&generate_unary_op_expr(
                unary_op_expr,
                prefix.clone() + "_in_unary_op_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->unary_op_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_unary_op_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::Subscript(subscript_expr) => {
            ret.push_str(&generate_subscript_expr(
                subscript_expr,
                prefix.clone() + "_in_subscript_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->subscript_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_subscript_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::Call(call_expr) => {
            ret.push_str(&generate_call_expr(
                call_expr,
                prefix.clone() + "_in_call_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->call_expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_call_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::Tuple(tuple) => {
            ret.push_str(&generate_tuple_expr(
                tuple,
                prefix.clone() + "_in_tuple_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->tuple__{}_\n",
                    prefix,
                    prefix.clone() + "_in_tuple_from_expr_"
                )
                .as_str(),
            );
        }
        Expr::Lit(lit_expr) => {
            ret.push_str(&generate_literal(lit_expr, prefix.clone()));
            ret.push_str(format!("expr__{}_-->literal__{}_\n", prefix, prefix).as_str());
        }
        Expr::Path(path) => {
            ret.push_str(
                format!(
                    "path_in_expr__{}_(({}))\nexpr__{}_-->path_in_expr__{}_\n",
                    prefix,
                    path.items.join("/"),
                    prefix,
                    prefix
                )
                .as_str(),
            );
        }
        Expr::Bracket(bracket_body) => {
            ret.push_str(&generate_bracket_body(
                bracket_body,
                prefix.clone() + "_in_bracket_from_expr_",
            ));
            ret.push_str(
                format!(
                    "expr__{}_-->bracket_body__{}_\n",
                    prefix,
                    prefix.clone() + "_in_bracket_from_expr_"
                )
                .as_str(),
            );
        }
    }
    ret
}

fn generate_vec_stmt(vec_stmt: &[Stmt], prefix: String) -> String {
    let mut ret = format!("vec_stmt__{}_((VecStmt))\n", prefix);
    for (stmt_cnt, i) in vec_stmt.iter().enumerate() {
        ret.push_str(&generate_stmt(
            i,
            prefix.clone() + "_in_stmt_from_vec__" + stmt_cnt.to_string().as_str() + "_",
        ));
        ret.push_str(
            format!(
                "vec_stmt__{}_-->stmt__{}_\n",
                prefix,
                prefix.clone() + "_in_stmt_from_vec__" + stmt_cnt.to_string().as_str() + "_"
            )
            .as_str(),
        );
    }
    ret
}

fn generate_stmt(stmt: &Stmt, prefix: String) -> String {
    let mut ret = format!("stmt__{}_((Stmt))\n", prefix);
    match stmt {
        Stmt::Let(let_stmt) => {
            ret.push_str(&generate_let_stmt(
                let_stmt,
                prefix.clone() + "_in_let_stmt_from_stmt_",
            ));
            ret.push_str(
                format!(
                    "stmt__{}_-->let_stmt__{}_\n",
                    prefix,
                    prefix.clone() + "_in_let_stmt_from_stmt_"
                )
                .as_str(),
            );
        }
        Stmt::While(while_stmt) => {
            ret.push_str(&generate_while_stmt(
                while_stmt,
                prefix.clone() + "_in_while_stmt_from_stmt_",
            ));
            ret.push_str(
                format!(
                    "stmt__{}_-->while_stmt__{}_\n",
                    prefix,
                    prefix.clone() + "_in_while_stmt_from_stmt_"
                )
                .as_str(),
            );
        }
        Stmt::For(for_stmt) => {
            ret.push_str(&generate_for_stmt(
                for_stmt,
                prefix.clone() + "_in_for_stmt_from_stmt_",
            ));
            ret.push_str(
                format!(
                    "stmt__{}_-->for_stmt__{}_\n",
                    prefix,
                    prefix.clone() + "_in_for_stmt_from_stmt_"
                )
                .as_str(),
            );
        }
        Stmt::Return => {
            ret.push_str(
                format!(
                    "ret__{}_((Return))\nstmt__{}_-->ret__{}_\n",
                    prefix, prefix, prefix
                )
                .as_str(),
            );
        }
        Stmt::Break => {
            ret.push_str(
                format!(
                    "break__{}_((Break))\nstmt__{}_-->break__{}_\n",
                    prefix, prefix, prefix
                )
                .as_str(),
            );
        }
        Stmt::Continue => {
            ret.push_str(
                format!(
                    "continue__{}_((Continue))\nstmt__{}_-->continue__{}_\n",
                    prefix, prefix, prefix
                )
                .as_str(),
            );
        }
        Stmt::Asgn(asgn_stmt) => {
            ret.push_str(&generate_asgn_stmt(
                asgn_stmt,
                prefix.clone() + "_in_asgn_stmt_from_stmt_",
            ));
            ret.push_str(
                format!(
                    "stmt__{}_-->asgn_stmt__{}_\n",
                    prefix,
                    prefix.clone() + "_in_asgn_stmt_from_stmt_"
                )
                .as_str(),
            );
        }
        Stmt::Expr(expr) => {
            ret.push_str(&generate_expr(expr, prefix.clone() + "_in_expr_from_stmt_"));
            ret.push_str(
                format!(
                    "stmt__{}_-->expr__{}_\n",
                    prefix,
                    prefix.clone() + "_in_expr_from_stmt_"
                )
                .as_str(),
            );
        }
    }
    ret
}

fn generate_asgn_stmt(asgn_stmt: &AsgnStmt, prefix: String) -> String {
    let mut ret = format!("asgn_stmt__{}_((Assign))\n", prefix);
    ret.push_str(&generate_expr(
        &asgn_stmt.lhs,
        prefix.clone() + "_lhs_from_asgn_stmt_",
    ));
    ret.push_str(
        format!(
            "asgn_stmt__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_lhs_from_asgn_stmt_"
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &asgn_stmt.rhs,
        prefix.clone() + "_rhs_from_asgn_stmt_",
    ));
    ret.push_str(
        format!(
            "asgn_stmt__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_rhs_from_asgn_stmt_"
        )
        .as_str(),
    );
    ret
}

fn generate_for_stmt(for_stmt: &ForStmt, prefix: String) -> String {
    let mut ret = format!("for_stmt__{}_((ForLoop))\n", prefix);
    ret.push_str(
        format!(
            "for_stmt_var_name__{}_(({}))\nfor_stmt__{}_-->for_stmt_var_name__{}_\n",
            prefix, for_stmt.var_name, prefix, prefix
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &for_stmt.range_l,
        prefix.clone() + "_in_l_range_from_for_stmt_",
    ));
    ret.push_str(
        format!(
            "for_stmt__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_in_l_range_from_for_stmt_"
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &for_stmt.range_l,
        prefix.clone() + "_in_r_range_from_for_stmt_",
    ));
    ret.push_str(
        format!(
            "for_stmt__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_in_r_range_from_for_stmt_"
        )
        .as_str(),
    );
    ret.push_str(&generate_bracket_body(&for_stmt.body, prefix.clone()));
    ret.push_str(format!("for_stmt__{}_-->bracket_body__{}_\n", prefix, prefix).as_str());
    ret
}

fn generate_while_stmt(while_stmt: &WhileStmt, prefix: String) -> String {
    let mut ret = format!("while_stmt__{}_((WhileStmt))\n", prefix);
    ret.push_str(&generate_expr(
        &while_stmt.condition,
        prefix.clone() + "_in_expr_from_while_stmt_",
    ));
    ret.push_str(
        format!(
            "while_stmt__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_in_expr_from_while_stmt_"
        )
        .as_str(),
    );
    ret.push_str(&generate_bracket_body(
        &while_stmt.body,
        prefix.clone() + "_in_bracket_from_while_",
    ));
    ret.push_str(
        format!(
            "while_stmt__{}_-->bracket_body__{}_\n",
            prefix,
            prefix.clone() + "_in_bracket_from_while_"
        )
        .as_str(),
    );
    ret
}

fn generate_let_stmt(let_stmt: &LetStmt, prefix: String) -> String {
    let mut ret = format!("let_stmt__{}_((LetStmt))\n", prefix);
    ret.push_str(
        format!(
            "let_stmt_var_name__{}_(({}))\nlet_stmt__{}_-->let_stmt_var_name__{}_\n",
            prefix, let_stmt.var_name, prefix, prefix
        )
        .as_str(),
    );
    ret.push_str(&generate_type(
        &let_stmt.typ,
        prefix.clone() + "_in_type_from_let_stmt_",
    ));
    ret.push_str(
        format!(
            "let_stmt__{}_-->type__{}_\n",
            prefix,
            prefix.clone() + "_in_type_from_let_stmt_"
        )
        .as_str(),
    );
    ret.push_str(&generate_expr(
        &let_stmt.expr,
        prefix.clone() + "_in_expr_from_let_stmt_",
    ));
    ret.push_str(
        format!(
            "let_stmt__{}_-->expr__{}_\n",
            prefix,
            prefix.clone() + "_in_expr_from_let_stmt_"
        )
        .as_str(),
    );
    ret
}

fn generate_vec_name_type_bind(vector: &[NameTypeBind], prefix: String) -> String {
    let mut ret = format!("vec_name_type_bind__{}_((VecNameTypeBind))\n", prefix);
    for (ret_cnt, i) in vector.iter().enumerate() {
        ret.push_str(
            generate_name_type_bind(i, prefix.clone() + ret_cnt.to_string().as_str()).as_str(),
        );
        ret.push_str(
            format!(
                "vec_name_type_bind__{}_-->name_type_bind__{}_\n",
                prefix,
                prefix.clone() + ret_cnt.to_string().as_str()
            )
            .as_str(),
        );
    }
    ret
}

fn generate_name_type_bind(bind: &NameTypeBind, prefix: String) -> String {
    let mut ret = format!("name_type_bind__{}_((NameTypeBind))\n", prefix);
    ret.push_str(
        format!(
            "name_type_bind_name__{}_(({}))\nname_type_bind__{}_-->name_type_bind_name__{}_\n",
            prefix, bind.var_name, prefix, prefix
        )
        .as_str(),
    );
    ret.push_str(generate_type(&bind.typ, prefix.clone() + "_in_type_bind_").as_str());
    ret.push_str(
        format!(
            "name_type_bind__{}_-->type__{}_\n",
            prefix,
            prefix.clone() + "_in_type_bind_"
        )
        .as_str(),
    );
    ret
}

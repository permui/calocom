use super::ast::*;
use super::frontend::parse;
use std::path::PathBuf;
#[allow(unused)]
use std::{fs, fmt::DebugTuple};

const HTML_PROVISION: &str = "<script src=\"https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js\"></script>
<script>
mermaid.initialize({startOnLoad:true});
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

pub fn generate_html(path: PathBuf) -> Result<(), String> {
	let source = match fs::read_to_string(path) {
		Ok(res) => res,
		Err(info) => return Err(info.to_string()),
	};
	let m = parse(&source);
	println!("{}", HTML_PROVISION);
	println!("<div class=\"mermaid\">\n%%{{init: {{'theme':'dark'}}}}%%\ngraph\n{}\n</div>\n", generate_imports(&m));
	println!("<div class=\"mermaid\">\n%%{{init: {{'theme':'dark'}}}}%%\ngraph\n{}\n</div>\n", generate_data_defs(&m));
	println!("<div class=\"mermaid\">\n%%{{init: {{'theme':'dark'}}}}%%\ngraph\n{}\n</div>\n", generate_func_defs(&m));
	Ok(())
}

fn generate_imports(m: &Module) -> String {
	let mut ret = String::from("imports((Imports))\n");
	let imports = &m.imports;
	let mut import_cnt = 0;
	for import in imports {
		let items = &import.items;
		let full_path: String = items.join(".");
		let cnt_string = import_cnt.to_string();
		let cnt_str = cnt_string.as_str();
		ret.push_str(format!("imports_{}_(({}))\nimports-->imports_{}_\n",cnt_str, full_path, cnt_str).as_str());
		import_cnt = import_cnt + 1;
	}
	ret
}

fn generate_data_defs(m: &Module) -> String {
	let mut ret = String::from("data_defs((Data Definitions))\n");
	let data_defs = &m.data_defs;
	let mut data_def_cnt = 0;
	for data_def in data_defs {
		ret.push_str(generate_data_def(data_def, data_def_cnt.to_string()).as_str());
		ret.push_str(format!("data_defs-->data_def__{}_\n", data_def_cnt.to_string().as_str()).as_str());
		data_def_cnt = data_def_cnt + 1;
	}
	ret
}

fn generate_data_def(m: &DataDef, prefix: String) -> String {
	let mut ret = format!("data_def__{}_((Data Definition))\n", prefix);
	let name = &m.name;
	let con_list = &m.con_list;
	ret.push_str(format!("data__{}_((data))\ndata_def__{}_-->data__{}_\n", prefix, prefix, prefix).as_str());
	ret.push_str(format!("name__{}_(({}))\ndata_def__{}_-->name__{}_\n", prefix, name, prefix, prefix).as_str());
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
			arrow_ret.push_str(generate_type(&first, prefix.clone() + "_0_").as_str());
			arrow_ret.push_str(generate_type(&second, prefix.clone() + "_1_").as_str());
			arrow_ret.push_str(format!("type_arrow__{}_-->type_arrow__{}__0_\n", prefix, prefix).as_str());
			arrow_ret.push_str(format!("type_arrow__{}_-->type_arrow__{}__1_\n", prefix, prefix).as_str());
			arrow_ret.push_str(format!("type__{}_-->type_arrow__{}_\n", prefix, prefix).as_str());
			arrow_ret
		},
		Type::Enum(first)=> {
			let mut enum_ret = format!("type_enum__{}_((Enum))\n", prefix);
			enum_ret.push_str(&generate_vec_constructor_type(first, prefix.clone() + "_").as_str());
			enum_ret.push_str(format!("type_enum__{}_-->type_vec_constructor_type__{}_\n", prefix, prefix.clone() + "_").as_str());
			enum_ret.push_str(format!("type__{}_-->type_enum__{}_\n", prefix, prefix).as_str());
			enum_ret
		},
		Type::Named(first) => {
			let mut named_ret = format!("type_named__{}_((Named))\n", prefix);
			named_ret.push_str(format!("type_named_string__{}_(({}))\ntype_named__{}_-->type_named_string__{}_\n", prefix, first, prefix, prefix).as_str());
			named_ret.push_str(format!("type__{}_-->type_named__{}_\n", prefix, prefix).as_str());
			named_ret
		},
		Type::Tuple(first) => {
			let mut tuple_ret = format!("type_tuple__{}_((Tuple))\n", prefix);
			let mut tuple_ret_cnt = 0;
			for i in first {
				tuple_ret.push_str(generate_type(i, prefix.clone() + tuple_ret_cnt.to_string().as_str()).as_str());
				tuple_ret.push_str(format!("type_tuple__{}_--> type__{}_\n", prefix, prefix.clone() + tuple_ret_cnt.to_string().as_str()).as_str());
				tuple_ret_cnt = tuple_ret_cnt + 1;
			}
			tuple_ret.push_str(format!("type__{}_-->type_tuple__{}_\n", prefix, prefix).as_str());
			tuple_ret
		},
		Type::Unit => {
			format!("type_unit__{}_((Unit))\ntype__{}_-->type_unit__{}_\n", prefix, prefix, prefix)
		},
        Type::Array(ptr) => {
            let mut array_ret = format!("type_array__{}_((Array))\n", prefix);
            array_ret.push_str(&generate_type(ptr, prefix.clone() + "_in_array_box_"));
            array_ret.push_str(format!("type_array__{}_-->type__{}_\n", prefix, prefix.clone() + "_in_array_box_").as_str());
            array_ret.push_str(format!("type__{}_-->type_array__{}_\n", prefix, prefix).as_str());
            array_ret
        }
	};
	ret.push_str(type_string.as_str());
	ret
}

fn generate_vec_constructor_type(vector: &Vec<ConstructorType>, prefix: String) -> String {
	let mut ret = format!("type_vec_constructor_type__{}_((VecConstructorType))\n", prefix);
	let mut ret_cnt = 0;
	for i in vector {
		ret.push_str(generate_construct_type(i, prefix.clone() + ret_cnt.to_string().as_str()).as_str());
		ret.push_str(format!("type_vec_constructor_type__{}_-->type_constructor_type__{}_\n", prefix, prefix.clone() + ret_cnt.to_string().as_str()).as_str());	
		ret_cnt = ret_cnt + 1;
	}
	ret
}

fn generate_construct_type(constructor_type: &ConstructorType, prefix: String) -> String {
	let mut ret = format!("type_constructor_type__{}_((ConstructorType))\n", prefix);
	ret.push_str(format!("type_constructor_type_name__{}_(({}))\n", prefix, constructor_type.name).as_str());
	ret.push_str(format!("type_constructor_type__{}_-->type_constructor_type_name__{}_\n", prefix, prefix).as_str());
	// if let Some(ref ano_type) = constructor_type.inner {
	// 	ret.push_str(generate_type(ano_type, prefix.clone() + "_").as_str());
	// 	ret.push_str(format!("type_constructor_type_{}-->type_{}\n", prefix, prefix.clone() + "_").as_str());
	// }
    let mut generate_cnt = 0;
    for i in &constructor_type.inner {
		ret.push_str(generate_type(i, prefix.clone() + "__" + &generate_cnt.to_string() + "_").as_str());
		ret.push_str(format!("type_constructor_type__{}_-->type__{}_\n", prefix, prefix.clone() + "__" + &generate_cnt.to_string() + "_").as_str());
        generate_cnt = generate_cnt + 1;
    }
	ret
}

fn generate_func_defs(m: &Module) -> String {
	let mut ret = String::from("func_defs((Function Definitions))\n");
	let mut ret_cnt = 0;
	for i in &m.func_defs {
		ret.push_str(generate_func_def(i, ret_cnt.to_string()).as_str());
		ret.push_str(format!("func_defs-->func_def__{}_\n", ret_cnt.to_string()).as_str());
		ret_cnt = ret_cnt + 1;
	}
	ret
}

fn generate_func_def(func_def: &FuncDef, prefix: String) -> String {
	let mut ret = format!("func_def__{}_((Function Definition))\n", prefix);
	ret.push_str(format!("func_def_name__{}_(({}))\nfunc_def__{}_-->func_def_name__{}_\n", prefix, func_def.name, prefix, prefix).as_str());	
	// ret.push_str(format!("func_def_left_param_paren__{}_((\"(\"))\nfunc_def__{}_-->func_def_left_param_paren__{}_\n", prefix, prefix, prefix).as_str());	
	ret.push_str(generate_vec_name_type_bind(&func_def.param_list, prefix.clone()).as_str());
	ret.push_str(format!("func_def__{}_-->vec_name_type_bind__{}_\n", prefix, prefix).as_str());
	// ret.push_str(format!("func_def_right_param_paren__{}_((\")\"))\nfunc_def__{}_-->func_def_right_param_paren__{}_\n", prefix, prefix, prefix).as_str());	
	ret.push_str(&generate_type(&func_def.ret_type, prefix.clone() + "_in_func_def_").as_str());
	ret.push_str(format!("func_def__{}_-->type__{}_\n", prefix, prefix.clone() + "_in_func_def_").as_str());
    ret.push_str(&generate_bracket_body(&func_def.body, prefix.clone() + "_in_bracket_body_").as_str());
    ret.push_str(format!("func_def__{}_-->bracket_body__{}_\n", prefix, prefix.clone() + "_in_bracket_body_").as_str());
	ret
}

fn generate_bracket_body(bracket_body: &BracketBody, prefix: String) -> String {
    let mut ret = format!("bracket_body__{}_((FuncBody))\n", prefix);
    ret.push_str(&generate_vec_stmt(&bracket_body.stmts, prefix.clone()));
    ret.push_str(format!("bracket_body__{}_-->vec_stmt__{}_\n", prefix, prefix).as_str());
    if let Some(ref ret_expr) = bracket_body.ret_expr {
        ret.push_str(&generate_expr(&ret_expr, prefix.clone() + "_in_expr_"));
        ret.push_str(format!("bracket_body__{}_-->expr__{}_\n", prefix, prefix.clone() + "_in_expr_" ).as_str());
    }
    ret
}

fn generate_expr(_expr: &Expr, prefix: String) -> String {
    let ret = format!("expr__{}_((Expr))\n", prefix);
    ret
}

fn generate_vec_stmt(vec_stmt: &Vec<Stmt>, prefix: String) -> String {
    let mut ret = format!("vec_stmt__{}_((VecStmt))\n", prefix);
    let mut stmt_cnt = 0;
    for i in vec_stmt {
        ret.push_str(&generate_stmt(i, prefix.clone() + "_in_stmt_from_vec__" + stmt_cnt.to_string().as_str() + "_"));
        ret.push_str(format!("vec_stmt__{}_-->stmt__{}_\n", prefix, prefix.clone() + "_in_stmt_from_vec__" + stmt_cnt.to_string().as_str() + "_").as_str());
        stmt_cnt = stmt_cnt + 1;
    }
    ret
}

fn generate_stmt(stmt: &Stmt, prefix: String) -> String {
    let mut ret = format!("stmt__{}_((Stmt))\n", prefix);
    match stmt {
        Stmt::Let(let_stmt) => {
            ret.push_str(&generate_let_stmt(let_stmt, prefix.clone() + "_in_let_stmt_from_stmt_"));
            ret.push_str(format!("stmt__{}_-->let_stmt__{}_\n", prefix, prefix.clone() + "_in_let_stmt_from_stmt_").as_str());
        },
        Stmt::While(while_stmt) => {
            ret.push_str(&generate_while_stmt(while_stmt, prefix.clone() + "_in_while_stmt_from_stmt_"));
            ret.push_str(format!("stmt__{}_-->while_stmt__{}_\n", prefix, prefix.clone() + "_in_while_stmt_from_stmt_").as_str());
        }
        Stmt::For(for_stmt) => {
            ret.push_str(&generate_for_stmt(for_stmt, prefix.clone() + "_in_for_stmt_from_stmt_"));
            ret.push_str(format!("stmt__{}_-->for_stmt__{}_\n", prefix, prefix.clone() + "_in_for_stmt_from_stmt_").as_str());
        },
        Stmt::Return => {
            ret.push_str(format!("ret__{}_((Return))\nstmt__{}_-->ret__{}_\n", prefix, prefix, prefix).as_str());
        },
        Stmt::Break => {
            ret.push_str(format!("break__{}_((Break))\nstmt__{}_-->break__{}_\n", prefix, prefix, prefix).as_str());
        },
        Stmt::Continue => {
            ret.push_str(format!("continue__{}_((Continue))\nstmt__{}_-->continue__{}_\n", prefix, prefix, prefix).as_str());
        },
        Stmt::Asgn(asgn_stmt) => {
            ret.push_str(&generate_asgn_stmt(asgn_stmt, prefix.clone() + "_in_asgn_stmt_from_stmt_"));
            ret.push_str(format!("stmt__{}_-->asgn_stmt__{}_\n", prefix, prefix.clone() + "_in_asgn_stmt_from_stmt_").as_str());
        },
        Stmt::Expr(expr) => {
            ret.push_str(&generate_expr(expr, prefix.clone() + "_in_expr_from_stmt_"));
            ret.push_str(format!("stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_in_expr_from_stmt_").as_str());
        },
    }
    ret
}

fn generate_asgn_stmt(asgn_stmt: &AsgnStmt, prefix: String) -> String {
    let mut ret = format!("asgn_stmt__{}_((Assign))\n", prefix);
    ret.push_str(&generate_expr(&asgn_stmt.lhs, prefix.clone() + "_lhs_from_asgn_stmt_"));
    ret.push_str(format!("asgn_stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_lhs_from_asgn_stmt_").as_str());
    ret.push_str(&generate_expr(&asgn_stmt.rhs, prefix.clone() + "_rhs_from_asgn_stmt_"));
    ret.push_str(format!("asgn_stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_rhs_from_asgn_stmt_").as_str());
    ret
}

fn generate_for_stmt(for_stmt: &ForStmt, prefix: String) -> String {    
    let mut ret = format!("for_stmt__{}_((ForLoop))\n", prefix);
    ret.push_str(format!("for_stmt_var_name__{}_(({}))\nfor_stmt__{}_-->for_stmt_var_name__{}_\n", prefix, for_stmt.var_name, prefix, prefix).as_str());
    ret.push_str(&generate_expr(&for_stmt.range_l, prefix.clone() + "_in_l_range_from_for_stmt_"));
    ret.push_str(format!("for_stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_in_l_range_from_for_stmt_").as_str());
    ret.push_str(&generate_expr(&for_stmt.range_l, prefix.clone() + "_in_r_range_from_for_stmt_"));
    ret.push_str(format!("for_stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_in_r_range_from_for_stmt_").as_str());
    ret.push_str(&generate_bracket_body(&for_stmt.body, prefix.clone()));
    ret.push_str(format!("for_stmt__{}_-->bracket_body__{}_\n", prefix, prefix).as_str());
    ret
}

fn generate_while_stmt(while_stmt: &WhileStmt, prefix: String) -> String {
    let mut ret = format!("while_stmt__{}_((WhileStmt))\n", prefix);
    ret.push_str(&generate_expr(&while_stmt.condition, prefix.clone() + "_in_expr_from_while_stmt_"));
    ret.push_str(format!("while_stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_in_expr_from_while_stmt_").as_str());
    ret.push_str(&generate_bracket_body(&while_stmt.body, prefix.clone() + "_in_bracket_from_while_"));
    ret.push_str(format!("while_stmt__{}_-->bracket_body__{}_\n", prefix, prefix.clone() + "_in_bracket_from_while_").as_str());
    ret
}

fn generate_let_stmt(let_stmt: &LetStmt, prefix: String) -> String {
    let mut ret = format!("let_stmt__{}_((LetStmt))\n", prefix);
    ret.push_str(format!("let_stmt_var_name__{}_(({}))\nlet_stmt__{}_-->let_stmt_var_name__{}_\n", prefix, let_stmt.var_name, prefix, prefix).as_str());
    ret.push_str(&generate_type(&let_stmt.typ, prefix.clone() + "_in_type_from_let_stmt_"));
    ret.push_str(format!("let_stmt__{}_-->type__{}_\n", prefix, prefix.clone() + "_in_type_from_let_stmt_").as_str());
    ret.push_str(&generate_expr(&let_stmt.expr, prefix.clone() + "_in_expr_from_let_stmt_"));
    ret.push_str(format!("let_stmt__{}_-->expr__{}_\n", prefix, prefix.clone() + "_in_expr_from_let_stmt_").as_str());
    ret
}

fn generate_vec_name_type_bind(vector: &Vec<NameTypeBind>, prefix: String) -> String {
	let mut ret = format!("vec_name_type_bind__{}_((VecNameTypeBind))\n", prefix);
	let mut ret_cnt = 0;
	for i in vector {
		ret.push_str(generate_name_type_bind(i, prefix.clone() + ret_cnt.to_string().as_str()).as_str());
		ret.push_str(format!("vec_name_type_bind__{}_-->name_type_bind__{}_\n", prefix, prefix.clone() + ret_cnt.to_string().as_str()).as_str());
		ret_cnt = ret_cnt + 1;
	}
	ret
}

fn generate_name_type_bind(bind: &NameTypeBind, prefix: String) -> String {
	let mut ret = format!("name_type_bind__{}_((NameTypeBind))\n", prefix);
	ret.push_str(format!("name_type_bind_name__{}_(({}))\nname_type_bind__{}_-->name_type_bind_name__{}_\n", prefix, bind.var_name, prefix, prefix).as_str());
	ret.push_str(generate_type(&bind.typ, prefix.clone() + "_in_type_bind_").as_str());
	ret.push_str(format!("name_type_bind__{}_-->type__{}_\n", prefix, prefix.clone() + "_in_type_bind_").as_str());
	ret
}
use calocom_compiler::frontend;
use std::fs;
use std::path::Path;

use inkwell::context::Context;

use calocom_compiler::backend::codegen::*;
use calocom_compiler::midend::middle_ir::MiddleIR;
use calocom_compiler::midend::typed_ast::TypedAST;

fn main() {
    let s = fs::read_to_string("example/test/simple.mag").expect("read file failed");
    let ast = frontend::parse(&s);
    let ty_ast: TypedAST = ast.into();
    fs::write("typed_ast.ir", format!("{:#?}", ty_ast)).expect("write failed");
    let mir: MiddleIR = ty_ast.into();
    fs::write("mir.ir", format!("{}", mir)).expect("write failed");
    let ctx = Context::create();
    let mut codegen = CodeGen::new("calocom", &ctx, &mir, Path::new("calocom_runtime.ll"));
    codegen.emit_all(&mir, Path::new("bitcode.bc"));
}

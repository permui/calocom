mod codegen;
mod memory;
mod runtime;

#[cfg(test)]
mod tests {

    use inkwell::context::Context;

    use super::codegen::*;
    use crate::frontend;
    use crate::midend::{middle_ir::MiddleIR, typed_ast::TypedAST};
    use std::fs;

    #[test]
    fn test_codegen() {
        let s = fs::read_to_string("../example/test/simple.mag").expect("read file failed");
        let ast = frontend::parse(&s);
        let ty_ast: TypedAST = ast.into();
        fs::write("../typed_ast.ir", format!("{:#?}", ty_ast)).expect("write failed");
        let mir: MiddleIR = ty_ast.into();
        fs::write("../mir.ir", format!("{}", mir)).expect("write failed");
        let ctx = Context::create();
        let mut codegen = CodeGen::new("calocom", &ctx, &mir);
        codegen.emit_all(&mir);
    }
}

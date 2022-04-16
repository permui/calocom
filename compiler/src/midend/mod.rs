mod middle_ir;
mod type_context;
mod typed_ast;
mod unique_name;

#[cfg(test)]
mod tests {
    use crate::{
        frontend,
        midend::{middle_ir::MiddleIR, typed_ast::TypedAST},
    };
    use std::fs;

    #[test]
    fn test_middle_ir() {
        let s = fs::read_to_string("../example/stage1/adt.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        let mir: MiddleIR = ast.into();
        println!("{:#?}", mir);
    }

    #[test]
    fn test_typed_ast() {
        let s = fs::read_to_string("../example/test/simple.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        let mir: TypedAST = ast.into();
        println!("{:#?}", mir);
    }
}

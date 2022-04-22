mod middle_ir;
mod type_context;
mod typed_ast;
mod unique_name;
mod name_decoration;

#[cfg(test)]
mod tests {
    use crate::{
        frontend,
        midend::{middle_ir::MiddleIR, typed_ast::TypedAST},
    };
    use std::fs;

    #[test]
    fn test() {
        let s = fs::read_to_string("../example/test/simple.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        let ty_ast: TypedAST = ast.into();
        let mir: MiddleIR = ty_ast.into();
        println!("{:#?}", mir);
    }
}

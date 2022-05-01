pub(crate) mod middle_ir;
pub(crate) mod name_decoration;
pub(crate) mod type_context;
pub(crate) mod typed_ast;
pub(crate) mod unique_name;

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
        fs::write("../typed_ast.ir", format!("{:#?}", ty_ast)).expect("write failed");
        let mir: MiddleIR = ty_ast.into();
        fs::write("../mir.ir", format!("{}", mir)).expect("write failed");
    }
}

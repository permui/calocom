mod middle_ir;
mod type_context;
mod unique_name;

#[cfg(test)]
mod tests {
    use crate::{frontend, midend::middle_ir::MiddleIR};
    use std::fs;

    #[test]
    fn test_codegen() {
        let s = fs::read_to_string("../example/stage1/adt.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        let mir: MiddleIR = ast.into();
        println!("{:#?}", mir);
    }
}

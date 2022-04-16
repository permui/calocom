use super::type_context::*;


trait DecorationName {
    fn get_name() -> String;
}

impl DecorationName for Type {
    fn get_name() -> String {
        todo!()
    }
}

fn decorate_polymorphic_function(
    path: Vec<String>,
    generic: Vec<&Type>,
    ret: &Type,
    arg: Vec<&Type>,
) {
}
fn decorate_function(path: Vec<String>, generic: Vec<&Type>, ret: &Type, arg: Vec<&Type>) {}

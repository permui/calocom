use crate::{common::type_context::TypeRef, ast::Literal};

pub struct PatternSymbol {
    unique_id: Vec<usize>,
}

pub enum PatternCtorEnum {
    Ctor(Option<(usize, TypeRef)>, Vec<PatternElement>),
    Literal(Literal),
    Wildcard,
}

pub struct PatternElement {
    path: PatternSymbol,
    ctor: PatternCtorEnum
}

pub struct PatternMatrix {
    content: Vec<Vec<PatternElement>>,
}

use super::type_context::*;

/*
Type Name Decoration Rules
TypeDecorationName  ::= ObjectName
                      | OpaqueName
                      | PrimitiveName
                      | EmptyTupleName
                      | TupleName FieldsName
                      | EnumerationName (ConstructorName)+
ObjectName      ::= 'Co'
OpaqueName      ::= 'Cp'
PrimitiveName   ::= 'Cu'
                  | 'Cb'
                  | 'Ci4'
                  | 'Cs'
EmptyTupleName  ::= 'Cy'
TupleName       ::= 'Ct'
EnumerationName ::= 'Ce'
ConstructorName ::= CtorName1
                  | CtorName2
CtorName1       ::= 'CFT' digits '_' digits identifier FieldsName
CtorName2       ::= 'CT' digits '_' digits identifier
FieldsName      ::= (FieldPosition FieldName)+
FieldPosition   ::= 'F' digits '_'
FieldName       ::= DecorationName

e.g:
    'Cu' encodes unit type
    'CeCT0_1OCFT1_1SF0_Cp' encodes Nat type
*/
trait DecorationName {
    fn get_decorated_name(&self) -> String;
}

impl DecorationName for Type {
    fn get_decorated_name(&self) -> String {
        match self {
            Type::Tuple(t) => {
                if t.fields.is_empty() {
                    "Cy".to_string()
                } else {
                    format!(
                        "Ct{}",
                        t.fields
                            .iter()
                            .enumerate()
                            .map(|(idx, ty)| format!("F{}_{}", idx, ty.get_decorated_name()))
                            .fold("".to_string(), |a, b| a + b.as_str())
                    )
                }
            }
            Type::Enum(e) => {
                assert!(!e.constructors.is_empty());
                format!(
                    "Ce{}",
                    e.constructors
                        .iter()
                        .enumerate()
                        .map(|(idx, (name, ty))| {
                            if let Some(ty) = ty {
                                let ty_vec = vec![ty];
                                format!(
                                    "CFT{}_{}{}{}",
                                    idx,
                                    name.len(),
                                    name,
                                    ty_vec
                                        .iter()
                                        .enumerate()
                                        .map(|(idx, ty)| format!(
                                            "F{}_{}",
                                            idx,
                                            ty.get_decorated_name()
                                        ))
                                        .fold("".to_string(), |a, b| a + b.as_str())
                                )
                            } else {
                                format!("CT{}_{}{}", idx, name.len(), name)
                            }
                        })
                        .fold("".to_string(), |a, b| a + b.as_str())
                )
            }
            Type::Primitive(prim) => match prim.typ {
                PrimitiveType::Object => "Co",
                PrimitiveType::Str => "Cs",
                PrimitiveType::Bool => "Cb",
                PrimitiveType::Int32 => "Ci4",
                PrimitiveType::Unit => "Cu",
            }
            .to_string(),
            Type::Opaque(_) => "Cp".to_string(),
        }
    }
}

// Function Name Decoration Rules
// FnDecorationName ::= '_C' PathName FunctionName ParametersName ReturnTypeName
// PathName         ::= ('M' digits identifier)*
// FunctionName     ::= 'PF' digits identifier
// ParametersName   ::= ('P' digits '_' TypeDecorationName)*
// ReturnTypeName   ::= 'RT' TypeDecorationName

pub fn decorate_polymorphic_function(
    path: &Vec<String>,
    _generic: &[&Type],
    ret: &Type,
    arg: &[&Type],
) -> String {
    let fn_name = path.last().unwrap();
    let path = &path[..path.len() - 1];
    format!(
        "_C{}{}{}{}",
        path.iter()
            .map(|s| format!("M{}{}", s.len(), s))
            .fold("".to_string(), |a, b| a + b.as_str()),
        format_args!("PF{}{}", fn_name.len(), fn_name),
        arg.iter()
            .enumerate()
            .map(|(idx, ty)| format!("P{}_{}", idx, ty.get_decorated_name()))
            .fold("".to_string(), |a, b| a + b.as_str()),
        format_args!("RT{}", ret.get_decorated_name())
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{frontend, midend::typed_ast::TypedAST};
    use std::fs;

    #[test]
    fn test_type_decoration() {
        let s = fs::read_to_string("../example/test/simple.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        let tast: TypedAST = ast.into();
        println!(
            "{:#?}",
            tast.ty_ctx
                .get_type_by_name("Nat")
                .unwrap()
                .1
                .get_decorated_name()
        );
        println!(
            "{:#?}",
            tast.ty_ctx
                .get_type_by_name("T1")
                .unwrap()
                .1
                .get_decorated_name()
        );
        println!(
            "{:#?}",
            tast.ty_ctx
                .get_type_by_name("T2")
                .unwrap()
                .1
                .get_decorated_name()
        );
    }
}

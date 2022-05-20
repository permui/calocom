/*
Name Mangling Rules

name ::= identifier-length identifier

// Primitive Types
type ::= 'Co'   // Calocom.Object
type ::= 'Cu'   // Calocom.Unit
type ::= 'Cb'   // Calocom.Bool
type ::= 'Ci4'  // Calocom.Int32
type ::= 'Cs'   // Calocom.String
type ::= 'Cci4' // Calocom.CInt32
type ::= 'Cf8'  // Calocom.Float64

// Complex Type
type-list ::= 'l_' type* '_l'
type ::= 'Ce' context name                  // Enum
type ::= 'Ct' type-list                     // Tuple
type ::= 'Cr' type                          // Reference
type ::= 'Ca' type                          // Array
type ::= 'Clf' function-signature           // Callable (Function)
type ::= 'Clc' function-signature           // Callable (Closure)
type ::= 'Clt' function-signature           // Callable (Ctor)

function-signature ::= 'f' type type-list
generic-signature  ::= 'g' number-of-generic-params
generic-function-signature ::= function-signature generic-signature
specialization     ::= 's' type-list

// Context
context ::= name*   // Full restricted context
context ::= '$'     // Current context

polymorphic-function-name ::= '_CALOCOM_PF' context name function-signature
specialized-function-name ::= '_CALOCOM_F'  context name generic-function-signature specialization
*/

use crate::common::{
    ref_path::ReferencePath,
    type_context::{CallKind, Primitive, Type, TypeContext, TypeRef},
};

pub trait Mangling {
    fn get_mangled_specialization(&self, list: &[TypeRef]) -> String;
    fn get_mangled_function_signature(&self, ret_type: TypeRef, params: &[TypeRef]) -> String;
    fn get_mangled_generic_function_signature(
        &self,
        ret_type: TypeRef,
        params: &[TypeRef],
        generic_params: usize,
    ) -> String;
    fn get_mangled_identifier<T: AsRef<str>>(ident: T) -> String {
        format!("{}{}", ident.as_ref().len(), ident.as_ref())
    }
    fn get_mangled_type_list(&self, list: &[TypeRef]) -> String;
    fn get_mangled_type_name(&self, typ: TypeRef) -> String;
    fn get_mangled_context_name<T: AsRef<str>>(path: Option<&dyn ReferencePath<T>>) -> String;
}

impl Mangling for TypeContext {
    fn get_mangled_function_signature(&self, ret_type: TypeRef, params: &[TypeRef]) -> String {
        format!(
            "f{}{}",
            self.get_mangled_type_name(ret_type),
            self.get_mangled_type_list(params)
        )
    }

    fn get_mangled_generic_function_signature(
        &self,
        ret_type: TypeRef,
        params: &[TypeRef],
        generic_params: usize,
    ) -> String {
        format!(
            "{}g{}",
            self.get_mangled_function_signature(ret_type, params),
            generic_params
        )
    }

    fn get_mangled_identifier<T: AsRef<str>>(ident: T) -> String {
        format!("{}{}", ident.as_ref().len(), ident.as_ref())
    }

    fn get_mangled_type_list(&self, list: &[TypeRef]) -> String {
        list.iter()
            .map(|field| self.get_mangled_type_name(*field))
            .fold(String::new(), |a, b| a + b.as_str())
    }

    fn get_mangled_type_name(&self, typ: TypeRef) -> String {
        let typ = self.types().get(typ).unwrap();
        match typ {
            Type::Tuple { fields } => {
                format!("Ctl_{}_l", self.get_mangled_type_list(fields))
            }
            Type::Enum { ctors: _, name } => {
                format!(
                    "Ce{}{}",
                    TypeContext::get_mangled_context_name::<String>(None),
                    name
                )
            }
            Type::Primitive(prim) => match prim {
                Primitive::Object => "Co",
                Primitive::Unit => "Cu",
                Primitive::Str => "Cs",
                Primitive::Bool => "Cb",
                Primitive::Int32 => "Ci4",
                Primitive::Float64 => "Cf8",
                Primitive::CInt32 => "Cci4",
            }
            .to_string(),
            Type::Opaque { alias } => {
                self.get_mangled_type_name(*alias.as_ref().left().expect("expect type index here"))
            }
            Type::Reference { refer } => format!(
                "Cr{}",
                self.get_mangled_type_name(*refer.as_ref().left().expect("expect type index here"))
            ),
            Type::Array(elem) => format!("Ca{}", self.get_mangled_type_name(*elem)),
            Type::Callable {
                ret_type,
                parameters,
                kind,
            } => format!(
                "{}{}",
                match kind {
                    CallKind::Function => "Clf",
                    CallKind::ClosureValue => "Clc",
                    CallKind::Constructor => "Clt",
                },
                self.get_mangled_function_signature(*ret_type, parameters)
            ),
        }
    }

    fn get_mangled_context_name<T: AsRef<str>>(path: Option<&dyn ReferencePath<T>>) -> String {
        if let Some(path) = path {
            path.full()
                .iter()
                .map(TypeContext::get_mangled_identifier)
                .reduce(|a, b| a + b.as_str())
                .expect("empty context path")
        } else {
            "$".to_string()
        }
    }

    fn get_mangled_specialization(&self, list: &[TypeRef]) -> String {
        format!("s{}", self.get_mangled_type_list(list))
    }
}

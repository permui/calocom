use std::{cell::RefCell, collections::HashMap, fmt::Debug, fmt::Display, panic, rc::Rc};

use super::unique_name::UniqueName;
use either::Either;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use strum::{EnumIter, IntoEnumIterator};
use Either::{Left, Right};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, TryFromPrimitive, IntoPrimitive, EnumIter)]
#[repr(usize)]
pub enum Primitive {
    Object = 0,
    Unit = 1,
    Str = 2,
    Bool = 3,
    Int32 = 4,
    Float64 = 5,
    CInt32 = 6,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallKind {
    Function,
    ClosureValue,
    Constructor,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Tuple {
        fields: Vec<Type>,
    },
    Enum {
        name: String,
        ctors: Vec<(String, Vec<Type>)>,
    },
    Primitive(Primitive),
    Opaque {
        alias: Either<usize, String>,
    },
    Reference {
        refer: Either<usize, String>,
    },
    Array(Box<Type>),
    Callable {
        kind: CallKind,
        ret_type: Box<Type>,
        parameters: Vec<Type>,
    },
}

impl From<Primitive> for Type {
    fn from(x: Primitive) -> Self {
        Type::Primitive(x)
    }
}

pub type TypeHandle = (usize, Type);

#[derive(Debug, Clone)]
pub struct TypeContext {
    name_typeid_map: HashMap<String, usize>,
    type_typeid_map: HashMap<Type, usize>,
    ctor_map: Rc<RefCell<HashMap<String, usize>>>,
    pub types: Vec<Type>,
}

impl Default for TypeContext {
    fn default() -> Self {
        let mut tcx = Self {
            name_typeid_map: Default::default(),
            type_typeid_map: Default::default(),
            types: Default::default(),
            ctor_map: Default::default(),
        };
        tcx.add_primitives();
        tcx
    }
}

impl TypeContext {
    pub fn get_idx_by_type(&self, typ: &Type) -> usize {
        *self.type_typeid_map.get(typ).unwrap()
    }

    pub fn get_type_by_idx(&self, idx: usize) -> Type {
        self.types[idx].clone()
    }

    pub fn singleton_type(&self, typ: Primitive) -> TypeHandle {
        (typ.into(), self.get_type_by_idx(typ.into()))
    }

    pub fn associate_name_and_idx(&mut self, name: &str, idx: usize) {
        if self.name_typeid_map.contains_key(name) {
            panic!("data type redefinition: {}", name);
        }
        self.name_typeid_map.insert(name.to_string(), idx);
    }

    pub fn get_ctor_type(&self, ctor: &str) -> Option<usize> {
        self.ctor_map.borrow().get(ctor).copied()
    }

    pub fn get_ctor_map(&self) -> Rc<RefCell<HashMap<String, usize>>> {
        self.ctor_map.clone()
    }

    pub fn get_ctor_index_and_field_type_by_name(
        &self,
        typ: usize,
        name: &str,
    ) -> (usize, Vec<TypeHandle>) {
        match &self.types[typ] {
            Type::Enum { ctors, name: _ } => {
                let ctor_idx = ctors
                    .iter()
                    .position(|ctor| ctor.0 == name)
                    .unwrap_or_else(|| panic!("{} not found", name));
                let ctor = &ctors[ctor_idx];
                (
                    ctor_idx,
                    ctor.1
                        .iter()
                        .map(|ty| (*self.type_typeid_map.get(ty).unwrap(), ty.clone()))
                        .collect(),
                )
            }
            _ => panic!("can't get fields of non enum type"),
        }
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<TypeHandle> {
        self.name_typeid_map
            .get(name)
            .map(|x| (*x, self.get_type_by_idx(*x)))
    }

    pub fn array_type(&mut self, elem: Type) -> TypeHandle {
        let res = Type::Array(Box::new(elem));
        self.insert_type_or_get(res)
    }

    pub fn tuple_type(&mut self, fields: Vec<Type>) -> TypeHandle {
        let res = Type::Tuple { fields };
        self.insert_type_or_get(res)
    }

    fn ctor_type(&mut self, typ: (Type, Vec<Type>)) -> TypeHandle {
        self.callable_type(CallKind::Constructor, typ.0, typ.1)
    }

    pub fn enum_type(&mut self, ctors: Vec<(String, Vec<Type>)>, name: String) -> TypeHandle {
        let res = Type::Enum {
            ctors: ctors.clone(),
            name,
        };
        let enum_type = self.insert_type_or_get(res);
        for ctor in ctors.into_iter() {
            if self.ctor_map.borrow().contains_key(&ctor.0) {
                panic!("multiple definitions for constructor name `{}`", ctor.0);
            }
            let ctor_type = self.ctor_type((enum_type.1.clone(), ctor.1));
            self.ctor_map.borrow_mut().insert(ctor.0, ctor_type.0);
        }
        enum_type
    }

    pub fn opaque_name_type(&mut self, name: &str) -> TypeHandle {
        let res = Type::Opaque {
            alias: Either::Right(name.to_string()),
        };
        self.insert_type_or_get(res)
    }

    pub fn opaque_type(&mut self, idx: usize) -> TypeHandle {
        assert!(idx < self.types.len());
        let res = Type::Opaque {
            alias: Either::Left(idx),
        };
        self.insert_type_or_get(res)
    }

    pub fn reference_type(&mut self, idx: usize) -> TypeHandle {
        assert!(idx < self.types.len());
        let res = Type::Reference {
            refer: Either::Left(idx),
        };
        self.insert_type_or_get(res)
    }

    pub fn callable_type(
        &mut self,
        kind: CallKind,
        ret_type: Type,
        parameters: Vec<Type>,
    ) -> TypeHandle {
        let res = Type::Callable {
            kind,
            ret_type: Box::new(ret_type),
            parameters,
        };
        self.insert_type_or_get(res)
    }

    fn insert_type_or_get(&mut self, typ: Type) -> TypeHandle {
        if let Some(id) = self.type_typeid_map.get(&typ) {
            return (*id, typ);
        }

        let self_index = self.types.len();
        self.types.push(typ.clone());
        self.type_typeid_map.insert(typ.clone(), self_index);

        (self_index, typ)
    }

    fn add_primitive(&mut self, primitive: Primitive, name: Option<&str>) {
        let idx: usize = primitive.into();
        let typ: Type = primitive.into();
        self.types[idx] = typ.clone();
        self.type_typeid_map.insert(typ, idx);
        if let Some(name) = name {
            self.name_typeid_map.insert(name.to_string(), idx);
        }
    }

    fn add_primitives(&mut self) {
        use Primitive::*;
        let prim = &[
            (Object, "__object!"),
            (Bool, "bool"),
            (Int32, "i32"),
            (Str, "str"),
            (Unit, "__unit!"),
            (CInt32, "__c_i32!"),
            (Float64, "f64"),
        ];
        let max_n: usize = Primitive::iter().map(|x| x.into()).max().unwrap();
        let max_n = max_n + 1;
        self.types.resize(max_n, Type::Opaque { alias: Left(0) });
        prim.iter()
            .for_each(|(ty, name)| self.add_primitive(*ty, Some(name)));
    }

    pub fn refine_all_type(&mut self) {
        for t in self.types.iter_mut() {
            TypeContext::refine_type(&self.name_typeid_map, t)
        }
        let mut new_node_map = HashMap::new();
        for idx in self.type_typeid_map.values() {
            new_node_map.insert(self.types[*idx].clone(), *idx);
        }
        self.type_typeid_map = new_node_map;
    }

    fn refine_type(name_map: &HashMap<String, usize>, t: &mut Type) {
        match t {
            Type::Tuple { fields } => {
                for field in fields {
                    TypeContext::refine_type(name_map, field);
                }
            }
            Type::Enum { ctors, name: _ } => {
                for ctor in ctors {
                    for field in &mut ctor.1 {
                        TypeContext::refine_type(name_map, field);
                    }
                }
            }
            Type::Array(elem) => {
                TypeContext::refine_type(name_map, elem);
            }
            Type::Primitive(_) => {}
            Type::Opaque { alias } => {
                if let Right(name) = alias {
                    if !name_map.contains_key(name) {
                        panic!("unresolved type {}", name);
                    }
                    let idx = *name_map.get(name).unwrap();
                    *alias = Left(idx);
                }
            }
            Type::Reference { refer } => {
                if let Right(name) = refer {
                    if !name_map.contains_key(name) {
                        panic!("unresolved type {}", name);
                    }
                    let idx = *name_map.get(name).unwrap();
                    *refer = Left(idx);
                }
            }
            Type::Callable {
                ret_type,
                parameters,
                kind: _,
            } => {
                TypeContext::refine_type(name_map, ret_type);
                for param in parameters {
                    TypeContext::refine_type(name_map, param);
                }
            }
        }
    }

    pub fn get_opaque_base_type(&self, typ: usize) -> usize {
        let mut typ = typ;
        loop {
            match self.get_type_by_idx(typ) {
                Type::Opaque { alias } => typ = alias.left().unwrap(),
                _ => return typ,
            }
        }
    }

    pub fn get_reference_base_type(&self, typ: usize) -> Option<usize> {
        match self.get_type_by_idx(typ) {
            Type::Reference { refer } => Some(refer.left().unwrap()),
            _ => None,
        }
    }

    pub fn is_t1_reference_of_t2(&self, t1: usize, t2: usize) -> bool {
        match self.get_type_by_idx(t1) {
            Type::Reference { refer } if self.is_type_eq(*refer.as_ref().left().unwrap(), t2) => {
                true
            }
            _ => false,
        }
    }

    pub fn is_enum_type(&self, t: usize) -> bool {
        matches!(self.get_type_by_idx(t), Type::Enum { ctors: _, name: _ })
    }

    pub fn is_tuple_type(&self, t: usize) -> bool {
        matches!(self.get_type_by_idx(t), Type::Tuple { fields: _ })
    }

    // if true, both types have the same type id
    pub fn is_type_purely_eq(&self, t1: usize, t2: usize) -> bool {
        t1 == t2
    }

    // if true, both types represent the same nominal type
    pub fn is_type_opaque_eq(&self, t1: usize, t2: usize) -> bool {
        self.get_opaque_base_type(t1) == self.get_opaque_base_type(t2)
    }

    // if true, both types are reference type
    // and the referred types represent the same nominal type
    pub fn is_type_reference_eq(&self, t1: usize, t2: usize) -> bool {
        matches!((
            self.get_reference_base_type(self.get_opaque_base_type(t1)),
            self.get_reference_base_type(self.get_opaque_base_type(t2)),
        ), (Some(t1), Some(t2)) if self.is_type_opaque_eq(t1, t2))
    }

    // if true, both types represent the same nominal type
    pub fn is_type_eq(&self, t1: usize, t2: usize) -> bool {
        self.is_type_purely_eq(t1, t2)
            || self.is_type_opaque_eq(t1, t2)
            || self.is_type_reference_eq(t1, t2)
    }

    // if true, both types are compatible when doing assignment
    pub fn is_compatible(&self, t1: usize, t2: usize) -> bool {
        self.is_type_eq(t1, t2) // the same nominal type
            || t1 == Primitive::Object.into() // unsafe cast due to polymorphism
            || t2 == Primitive::Object.into() // unsafe cast due to polymorphism
            || self.is_t1_reference_of_t2(t1, t2) // one is reference and the other is the referred type
            || self.is_t1_reference_of_t2(t2, t1)
    }

    pub fn is_callable_type(&self, t: usize) -> bool {
        matches!(
            self.get_type_by_idx(t),
            Type::Callable {
                ret_type: _,
                parameters: _,
                kind: _
            }
        )
    }

    pub fn is_array_type(&self, t: usize) -> bool {
        matches!(self.get_type_by_idx(t), Type::Array(_))
    }

    pub fn is_index_type(&self, t: usize) -> bool {
        self.is_type_eq(t, Primitive::Int32.into())
    }

    pub fn is_arithmetic_type(&self, t: usize) -> bool {
        self.is_type_eq(t, Primitive::Float64.into()) || self.is_type_eq(t, Primitive::Int32.into())
    }

    pub fn is_boolean_testable_type(&self, t: usize) -> bool {
        self.is_type_eq(t, Primitive::Bool.into())
    }

    pub fn is_partially_ordered_type(&self, t: usize) -> bool {
        self.is_totally_ordered_type(t) || self.is_type_eq(t, Primitive::Float64.into())
    }

    pub fn is_partially_equal_type(&self, t: usize) -> bool {
        self.is_totally_equal_type(t) || self.is_type_eq(t, Primitive::Float64.into())
    }

    pub fn is_totally_ordered_type(&self, t: usize) -> bool {
        self.is_type_eq(t, Primitive::Int32.into())
    }

    pub fn is_totally_equal_type(&self, t: usize) -> bool {
        self.is_type_eq(t, Primitive::Int32.into())
            || self.is_type_eq(t, Primitive::Str.into())
            || self.is_type_eq(t, Primitive::Bool.into())
    }

    pub fn substitute_all_opaque_references(&mut self, type_map: &HashMap<usize, String>) {
        for t in self.types.iter_mut() {
            TypeContext::substitute_opaque_reference(type_map, t)
        }
    }

    pub fn substitute_opaque_reference(type_map: &HashMap<usize, String>, t: &mut Type) {
        match t {
            Type::Tuple { fields } => {
                for field in fields {
                    TypeContext::substitute_opaque_reference(type_map, field);
                }
            }
            Type::Enum { ctors, name: _ } => {
                for ctor in ctors {
                    for field in &mut ctor.1 {
                        TypeContext::substitute_opaque_reference(type_map, field);
                    }
                }
            }
            Type::Primitive(_) => {}
            Type::Opaque { alias } => {
                if let Left(typ) = alias {
                    if !type_map.contains_key(typ) {
                        panic!("can't found type {}", typ);
                    }
                    let name = type_map.get(typ).unwrap().clone();
                    *alias = Right(name);
                }
            }
            Type::Reference { refer } => {
                if let Left(typ) = refer {
                    if !type_map.contains_key(typ) {
                        panic!("can't found type {}", typ);
                    }
                    let name = type_map.get(typ).unwrap().clone();
                    *refer = Right(name);
                }
            }
            Type::Array(elem) => TypeContext::substitute_opaque_reference(type_map, elem),
            Type::Callable {
                ret_type,
                parameters,
                kind: _,
            } => {
                TypeContext::substitute_opaque_reference(type_map, ret_type);
                for param in parameters.iter_mut() {
                    TypeContext::substitute_opaque_reference(type_map, param);
                }
            }
        }
    }

    pub fn get_display_name_map(&self) -> (Self, HashMap<usize, String>) {
        let mut context = self.clone();
        let mut display_name_map = HashMap::new();
        let mut namer = UniqueName::new();
        for (k, v) in context.name_typeid_map.iter() {
            display_name_map.insert(*v, k.clone());
        }

        for (idx, _) in context.types.iter().enumerate() {
            display_name_map
                .entry(idx)
                .or_insert_with(|| namer.next_name("anonymous_type"));
        }

        context.substitute_all_opaque_references(&display_name_map);
        (context, display_name_map)
    }
}

impl Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Primitive::Object => write!(f, "__object"),
            Primitive::Str => write!(f, "str"),
            Primitive::Bool => write!(f, "bool"),
            Primitive::Int32 => write!(f, "i32"),
            Primitive::Unit => write!(f, "__unit"),
            Primitive::CInt32 => write!(f, "__c_i32"),
            Primitive::Float64 => write!(f, "f64"),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Tuple { fields } => {
                write!(f, "(")?;
                let field_str = fields.iter().fold(String::new(), |acc, item| {
                    if acc.is_empty() {
                        format!("{}", item)
                    } else {
                        format!("{}, {}", acc, item)
                    }
                });
                write!(f, "{}", field_str)?;
                write!(f, ")")
            }
            Type::Enum { ctors, name: _ } => {
                write!(f, "{{")?;
                let item2str = |item: &(String, Vec<Type>)| {
                    format!(
                        "<{} {}>",
                        item.0,
                        Type::Tuple {
                            fields: item.1.clone()
                        }
                    )
                };
                let field_str = ctors.iter().fold(String::new(), |acc, item| {
                    if acc.is_empty() {
                        item2str(item)
                    } else {
                        format!("{} | {}", acc, item2str(item))
                    }
                });
                write!(f, "{}", field_str)?;
                write!(f, "}}")
            }
            Type::Primitive(p) => write!(f, "{}", p),
            Type::Opaque { alias } => {
                write!(f, "{}", alias.as_ref().right().unwrap())
            }
            Type::Reference { refer } => {
                write!(f, "ref {}", refer.as_ref().right().unwrap())
            }
            Type::Array(arr) => write!(f, "[{}]", arr),
            Type::Callable {
                ret_type,
                parameters,
                kind: _,
            } => {
                write!(
                    f,
                    "{} -> {}",
                    Type::Tuple {
                        fields: parameters.clone()
                    },
                    ret_type
                )
            }
        }
    }
}

impl Display for TypeContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (context, map) = self.get_display_name_map();

        writeln!(f, "TypeContext {{")?;
        for (idx, typ) in context.types.iter().enumerate() {
            writeln!(f, "    type[{}] {}: {}", idx, map.get(&idx).unwrap(), typ)?;
        }
        write!(f, "}}")
    }
}

use std::{
    collections::HashMap,
    fmt::Debug,
    fmt::{format, Display},
    panic,
};

use super::{middle_ir::SymTable, unique_name::UniqueName};
use either::Either;
use Either::{Left, Right};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Tuple {
    pub fields: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Enum {
    pub constructors: Vec<(String, Vec<Type>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    Object,
    Str,
    Bool,
    Int32,
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Primitive {
    pub typ: PrimitiveType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Opaque {
    pub refer: Either<usize, String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Tuple(Box<Tuple>),
    Enum(Box<Enum>),
    Primitive(Primitive),
    Opaque(Opaque),
}

impl From<Type> for Opaque {
    fn from(x: Type) -> Self {
        match x {
            Type::Opaque(x) => x,
            _ => panic!("not an opaque type"),
        }
    }
}

impl From<Tuple> for Type {
    fn from(x: Tuple) -> Self {
        Type::Tuple(Box::new(x))
    }
}

impl From<Enum> for Type {
    fn from(x: Enum) -> Self {
        Type::Enum(Box::new(x))
    }
}

impl From<Primitive> for Type {
    fn from(x: Primitive) -> Self {
        Type::Primitive(x)
    }
}

impl From<Opaque> for Type {
    fn from(x: Opaque) -> Self {
        Type::Opaque(x)
    }
}

impl From<PrimitiveType> for Type {
    fn from(x: PrimitiveType) -> Self {
        Primitive { typ: x }.into()
    }
}

pub type TypeHandle = (usize, Type);

#[derive(Debug, Default)]
pub struct SingletonType {}

impl SingletonType {
    pub const OBJECT: usize = 0;
    pub const BOOL: usize = 1;
    pub const I32: usize = 2;
    pub const STR: usize = 3;
    pub const UNIT: usize = 4;
    pub fn is_singleton_type(typ: usize) -> bool {
        matches!(
            typ,
            SingletonType::OBJECT
                | SingletonType::BOOL
                | SingletonType::I32
                | SingletonType::UNIT
                | SingletonType::STR
        )
    }
}

impl From<PrimitiveType> for usize {
    fn from(typ: PrimitiveType) -> Self {
        match typ {
            PrimitiveType::Str => SingletonType::STR,
            PrimitiveType::Bool => SingletonType::BOOL,
            PrimitiveType::Int32 => SingletonType::I32,
            PrimitiveType::Unit => SingletonType::UNIT,
            PrimitiveType::Object => SingletonType::OBJECT,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeContext {
    name_typeid_map: HashMap<String, usize>,
    type_typeid_map: HashMap<Type, usize>,
    types: Vec<Type>,
    ftypes: HashMap<String, (usize, Vec<usize>)>,
    ext_poly_ftypes: HashMap<Vec<String>, (usize, Vec<usize>)>,
    pub env: SymTable<usize>,
}

impl Default for TypeContext {
    fn default() -> Self {
        let mut tcx = Self {
            name_typeid_map: Default::default(),
            type_typeid_map: Default::default(),
            types: Default::default(),
            ftypes: Default::default(),
            ext_poly_ftypes: Default::default(),
            env: Default::default(),
        };
        tcx.add_primitives();
        tcx
    }
}

impl TypeContext {
    pub fn get_type_by_idx(&self, idx: usize) -> TypeHandle {
        (idx, self.types[idx].clone())
    }

    pub fn find_external_polymorphic_function_type(
        &self,
        path: &[String],
    ) -> Option<&(usize, Vec<usize>)> {
        self.ext_poly_ftypes.get(path)
    }

    pub fn associate_external_polymorphic_function_type(
        &mut self,
        path: &[String],
        typ: (usize, Vec<usize>),
    ) {
        if self.ext_poly_ftypes.contains_key(path) {
            panic!("external polymorphic function redefined");
        }
        self.ext_poly_ftypes.insert(path.into(), typ);
    }

    pub fn find_function_type(&self, name: &str) -> Option<&(usize, Vec<usize>)> {
        self.ftypes.get(name)
    }

    pub fn associate_function_type(&mut self, name: &str, typ: (usize, Vec<usize>)) {
        if self.ftypes.contains_key(name) {
            panic!("function {} redefined", name);
        }
        self.ftypes.insert(name.to_string(), typ);
    }

    pub fn singleton_type(&self, typ: PrimitiveType) -> TypeHandle {
        self.get_type_by_idx(typ.into())
    }

    pub fn associate_name_and_idx(&mut self, name: &str, idx: usize) {
        if self.name_typeid_map.contains_key(name) {
            panic!("data type redefinition: {}", name);
        }
        self.name_typeid_map.insert(name.to_string(), idx);
    }

    pub fn get_ctor_field_type_by_name(&self, typ: usize, name: &str) -> Vec<TypeHandle> {
        match &self.types[typ] {
            Type::Enum(e) => {
                let ctor_idx = e
                    .constructors
                    .iter()
                    .position(|ctor| ctor.0 == name)
                    .unwrap_or_else(|| panic!("{} not found", name));
                let ctor = &e.constructors[ctor_idx];
                ctor.1
                    .iter()
                    .map(|ty| (*self.type_typeid_map.get(ty).unwrap(), ty.clone()))
                    .collect()
            }
            _ => panic!("can't get fields of non enum type"),
        }
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<TypeHandle> {
        self.name_typeid_map
            .get(name)
            .map(|x| self.get_type_by_idx(*x))
    }

    pub fn tuple_type(&mut self, fields: Vec<Type>) -> TypeHandle {
        let res = Tuple { fields }.into();
        self.insert_type_or_get(res)
    }

    pub fn enum_type(&mut self, constructors: Vec<(String, Vec<Type>)>) -> TypeHandle {
        let res = Enum { constructors }.into();
        self.insert_type_or_get(res)
    }

    pub fn opaque_name_type(&mut self, name: &str) -> TypeHandle {
        let res = Opaque {
            refer: Either::Right(name.to_string()),
        }
        .into();
        self.insert_type_or_get(res)
    }

    pub fn opaque_type(&mut self, idx: usize) -> TypeHandle {
        assert!(idx < self.types.len());
        let res = Opaque {
            refer: Either::Left(idx),
        }
        .into();
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

    fn add_primitive(&mut self, primitive: PrimitiveType, name: Option<&str>) {
        let idx: usize = primitive.clone().into();
        let typ: Type = primitive.into();
        self.types.push(typ.clone());
        self.type_typeid_map.insert(typ, idx);
        if let Some(name) = name {
            self.name_typeid_map.insert(name.to_string(), idx);
        }
    }

    fn add_primitives(&mut self) {
        // NOTE: be the same order with constants in SingletonType
        self.add_primitive(PrimitiveType::Object, Some("__object"));
        self.add_primitive(PrimitiveType::Bool, Some("bool"));
        self.add_primitive(PrimitiveType::Int32, Some("i32"));
        self.add_primitive(PrimitiveType::Str, Some("str"));
        self.add_primitive(PrimitiveType::Unit, Some("__unit"));
    }

    pub fn refine_all_opaque_type(&mut self) {
        for t in self.types.iter_mut() {
            TypeContext::refine_opaque_type(&self.name_typeid_map, t)
        }
        let mut new_node_map = HashMap::new();
        for idx in self.type_typeid_map.values() {
            new_node_map.insert(self.types[*idx].clone(), *idx);
        }
        self.type_typeid_map = new_node_map;
    }

    fn refine_opaque_type(name_map: &HashMap<String, usize>, t: &mut Type) {
        match t {
            Type::Tuple(tuple) => {
                let Tuple { fields } = tuple.as_mut();
                for field in fields {
                    TypeContext::refine_opaque_type(name_map, field);
                }
            }
            Type::Enum(enu) => {
                let Enum { constructors } = enu.as_mut();
                for ctor in constructors {
                    for field in &mut ctor.1 {
                        TypeContext::refine_opaque_type(name_map, field);
                    }
                }
            }
            Type::Primitive(_) => {}
            Type::Opaque(opaque) => {
                let Opaque { refer } = opaque;
                if let Right(name) = refer {
                    if !name_map.contains_key(name) {
                        panic!("unresolved type {}", name);
                    }
                    let idx = *name_map.get(name).unwrap();
                    *refer = Left(idx);
                }
            }
        }
    }

    fn collect_constructor(record: &mut HashMap<String, usize>, idx: usize, ty: &Type) {
        if let Type::Enum(enu) = ty {
            let Enum { constructors } = enu.as_ref();
            for ctor in constructors {
                record.insert(ctor.0.clone(), idx);
            }
        }
    }

    pub fn collect_all_constructor(&self, constructors: &mut HashMap<String, usize>) {
        for (idx, ty) in self.types.iter().enumerate() {
            TypeContext::collect_constructor(constructors, idx, ty);
        }
    }

    pub fn get_opaque_base_type(&self, typ: usize) -> usize {
        let mut typ = typ;
        loop {
            match self.get_type_by_idx(typ).1 {
                Type::Opaque(opaque) => typ = opaque.refer.left().unwrap(),
                _ => return typ,
            }
        }
    }

    pub fn is_t1_opaque_of_t2(&self, t1: usize, t2: usize) -> bool {
        match self.get_type_by_idx(t1).1 {
            Type::Opaque(opaque) => *opaque.refer.as_ref().left().unwrap() == t2,
            _ => false,
        }
    }

    pub fn is_enum_type(&self, t: usize) -> bool {
        matches!(self.get_type_by_idx(t).1, Type::Enum(_))
    }

    pub fn is_type_pure_eq(&self, t1: usize, t2: usize) -> bool {
        t1 == t2
    }

    pub fn is_type_opaque_eq(&self, t1: usize, t2: usize) -> bool {
        let t1 = self.get_type_by_idx(t1).1;
        let t2 = self.get_type_by_idx(t2).1;
        match (t1, t2) {
            (Type::Opaque(opaque1), Type::Opaque(opaque2)) => self.is_type_eq(
                *opaque1.refer.as_ref().left().unwrap(),
                *opaque2.refer.as_ref().left().unwrap(),
            ),
            _ => false,
        }
    }

    pub fn is_type_eq(&self, t1: usize, t2: usize) -> bool {
        self.is_type_pure_eq(t1, t2) || self.is_type_opaque_eq(t1, t2)
    }

    pub fn is_compatible(&self, t1: usize, t2: usize) -> bool {
        self.is_type_eq(t1, t2)
            || t1 == SingletonType::OBJECT
            || t2 == SingletonType::OBJECT
            || self.is_t1_opaque_of_t2(t1, t2)
            || self.is_t1_opaque_of_t2(t2, t1)
    }

    pub fn substitute_all_opaque_references(&mut self, type_map: &HashMap<usize, String>) {
        for t in self.types.iter_mut() {
            TypeContext::substitute_opaque_reference(type_map, t)
        }
    }

    pub fn substitute_opaque_reference(type_map: &HashMap<usize, String>, t: &mut Type) {
        match t {
            Type::Tuple(tuple) => {
                let Tuple { fields } = tuple.as_mut();
                for field in fields {
                    TypeContext::substitute_opaque_reference(type_map, field);
                }
            }
            Type::Enum(enu) => {
                let Enum { constructors } = enu.as_mut();
                for ctor in constructors {
                    for field in &mut ctor.1 {
                        TypeContext::substitute_opaque_reference(type_map, field);
                    }
                }
            }
            Type::Primitive(_) => {}
            Type::Opaque(opaque) => {
                let Opaque { refer } = opaque;
                if let Left(typ) = refer {
                    if !type_map.contains_key(typ) {
                        panic!("can't found type {}", typ);
                    }
                    let name = type_map.get(typ).unwrap().clone();
                    *refer = Right(name);
                }
            }
        }
    }
}
impl Display for Tuple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        let field_str = self.fields.iter().fold(String::new(), |acc, item| {
            if acc.is_empty() {
                format!("{}", item)
            } else {
                format!("{}, {}", acc, item)
            }
        });
        write!(f, "{}", field_str)?;
        write!(f, ")")
    }
}

impl Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.typ {
            PrimitiveType::Object => write!(f, "__object"),
            PrimitiveType::Str => write!(f, "str"),
            PrimitiveType::Bool => write!(f, "bool"),
            PrimitiveType::Int32 => write!(f, "i32"),
            PrimitiveType::Unit => write!(f, "__unit"),
        }
    }
}

impl Display for Enum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let item2str = |item: &(String, Vec<Type>)| {
            format!(
                "<{} {}>",
                item.0,
                Tuple {
                    fields: item.1.clone()
                }
            )
        };
        let field_str = self.constructors.iter().fold(String::new(), |acc, item| {
            if acc.is_empty() {
                item2str(item)
            } else {
                format!("{} | {}", acc, item2str(item))
            }
        });
        write!(f, "{}", field_str)?;
        write!(f, "]")
    }
}

impl Display for Opaque {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ref {}", self.refer.as_ref().right().unwrap())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Tuple(t) => write!(f, "{}", t),
            Type::Enum(e) => write!(f, "{}", e),
            Type::Primitive(p) => write!(f, "{}", p),
            Type::Opaque(o) => write!(f, "{}", o),
        }
    }
}

impl Display for TypeContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

        writeln!(f, "TypeContext {{")?;

        for (idx, typ) in context.types.iter().enumerate() {
            writeln!(f, "    {}: {}", display_name_map.get(&idx).unwrap(), typ)?;
        }

        write!(f, "}}")
    }
}

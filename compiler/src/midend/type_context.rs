use std::{collections::{HashMap, HashSet}, panic};

use either::Either;
use Either::{Left, Right};

use super::middle_ir::SymTable;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Tuple {
    fields: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Enum {
    constructors: Vec<(String, Option<Type>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    Str,
    Bool,
    Int32,
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Primitive {
    typ: PrimitiveType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Opaque {
    refer: Either<usize, String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Tuple(Box<Tuple>),
    Enum(Box<Enum>),
    Primitive(Primitive),
    Opaque(Opaque),
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

pub type TypeHandle = (usize, Type);

#[derive(Debug, Default)]
pub struct SingletonType {
    bool: usize,
    i32: usize,
    str: usize,
    unit: usize,
}

#[derive(Debug)]
pub struct TypeContext {
    name_typeid_map: HashMap<String, usize>,
    type_typeid_map: HashMap<Type, usize>,
    types: Vec<Type>,
    stypes: SingletonType,
    ftypes: HashMap<String, (usize, Vec<usize>)>,
    pub env: SymTable<usize>,
}

impl Default for TypeContext {
    fn default() -> Self {
        let mut tcx = Self {
            name_typeid_map: Default::default(),
            type_typeid_map: Default::default(),
            types: Default::default(),
            stypes: Default::default(),
            ftypes: Default::default(),
            env: Default::default(),
        };
        tcx.add_primitive();
        tcx
    }
}

impl TypeContext {
    fn get_type_by_idx(&self, idx: usize) -> TypeHandle {
        (idx, self.types[idx].clone())
    }

    pub fn associate_function_type(&mut self, name: &str, typ: (usize, Vec<usize>)) {
        if self.ftypes.contains_key(name) {
            panic!("function {} redefined", name);
        }
        self.ftypes.insert(name.to_string(), typ);
    }

    pub fn singleton_type(&self, typ: PrimitiveType) -> TypeHandle {
        match typ {
            PrimitiveType::Str => self.get_type_by_idx(self.stypes.str),
            PrimitiveType::Bool => self.get_type_by_idx(self.stypes.bool),
            PrimitiveType::Int32 => self.get_type_by_idx(self.stypes.i32),
            PrimitiveType::Unit => self.get_type_by_idx(self.stypes.unit),
        }
    }

    pub fn associate_name_and_idx(&mut self, name: &str, idx: usize) {
        if self.name_typeid_map.contains_key(name) {
            panic!("data type redefinition: {}", name);
        }
        self.name_typeid_map.insert(name.to_string(), idx);
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<TypeHandle> {
        if self.name_typeid_map.contains_key(name) {
            let idx = *self.name_typeid_map.get(name).unwrap();
            Some(self.get_type_by_idx(idx))
        } else {
            None
        }
    }

    pub fn tuple_type(&mut self, fields: Vec<Type>) -> TypeHandle {
        let res = Tuple { fields }.into();
        self.insert_type_or_get(res)
    }

    pub fn enum_type(&mut self, constructors: Vec<(String, Option<Type>)>) -> TypeHandle {
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
        if self.type_typeid_map.contains_key(&typ) {
            return (*self.type_typeid_map.get(&typ).unwrap(), typ);
        }

        let self_index = self.types.len();
        self.types.push(typ.clone());
        self.type_typeid_map.insert(typ.clone(), self_index);

        (self_index, typ)
    }

    fn add_primitive(&mut self) {
        let b: Type = Primitive {
            typ: PrimitiveType::Bool,
        }
        .into();

        let i: Type = Primitive {
            typ: PrimitiveType::Int32,
        }
        .into();

        let u: Type = Primitive {
            typ: PrimitiveType::Unit,
        }
        .into();

        let s: Type = Primitive {
            typ: PrimitiveType::Str,
        }
        .into();

        self.types.clear();

        let (bi, ii, ui, si) = (0, 1, 2, 3);

        self.types.push(b.clone());
        self.types.push(i.clone());
        self.types.push(u.clone());
        self.types.push(s.clone());

        self.type_typeid_map.insert(b, bi);
        self.type_typeid_map.insert(i, ii);
        self.type_typeid_map.insert(u, ui);
        self.type_typeid_map.insert(s, si);

        self.name_typeid_map.insert("bool".to_string(), bi);
        self.name_typeid_map.insert("i32".to_string(), ii);
        self.name_typeid_map.insert("str".to_string(), si);

        self.stypes = SingletonType {
            bool: bi,
            i32: ii,
            str: si,
            unit: ui,
        };
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

    fn collect_constructor(record: &mut HashSet<String>, ty: &Type) {
        if let Type::Enum(enu) = ty {
            let Enum { constructors } = enu.as_ref();
            for ctor in constructors {
                record.insert(ctor.0.clone());
            }
        }
    }

    pub fn collect_all_constructor(&self, constructors: &mut HashSet<String>) {
        for ty in self.types.iter() {
            TypeContext::collect_constructor(constructors, ty)
        }
    }
}

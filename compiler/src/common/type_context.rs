use std::{cell::RefCell, collections::HashMap, fmt::Debug, fmt::Display, panic, rc::Rc};

use super::unique_name::UniqueName;
use either::Either;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use slotmap::{new_key_type, SlotMap};
use std::fmt::Write;
use strum::EnumIter;
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

new_key_type! {
    pub struct TypeRef;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Tuple {
        fields: Vec<TypeRef>,
    },
    Enum {
        name: String,
        ctors: Vec<(String, Vec<TypeRef>)>,
    },
    Primitive(Primitive),
    Opaque {
        alias: Either<TypeRef, String>,
    },
    Reference {
        refer: Either<TypeRef, String>,
    },
    Array(TypeRef),
    Callable {
        kind: CallKind,
        ret_type: TypeRef,
        parameters: Vec<TypeRef>,
    },
}

impl From<Primitive> for Type {
    fn from(x: Primitive) -> Self {
        Type::Primitive(x)
    }
}

#[derive(Debug, Clone)]
pub struct TypeContext {
    name_ref_map: HashMap<String, TypeRef>,
    type_ref_map: HashMap<Type, TypeRef>,
    prim_ref_map: [TypeRef; 7],
    ctor_map: Rc<RefCell<HashMap<String, TypeRef>>>,
    types: SlotMap<TypeRef, Type>,
}

impl Default for TypeContext {
    fn default() -> Self {
        let mut tcx = Self {
            name_ref_map: Default::default(),
            type_ref_map: Default::default(),
            types: Default::default(),
            ctor_map: Default::default(),
            prim_ref_map: Default::default(),
        };
        tcx.add_primitives();
        tcx
    }
}

impl TypeContext {
    pub const PRIMITIVE_TYPE_NAME: [&'static str; 7] = [
        "__object!",
        "__unit!",
        "str",
        "bool",
        "i32",
        "f64",
        "__c_i32!",
    ];

    pub fn types(&self) -> &SlotMap<TypeRef, Type> {
        &self.types
    }

    pub fn get_ref_by_type(&self, typ: &Type) -> TypeRef {
        *self.type_ref_map.get(typ).unwrap()
    }

    pub fn get_type_by_ref(&self, type_ref: TypeRef) -> Type {
        self.types.get(type_ref).unwrap().clone()
    }

    pub fn singleton_type(&self, typ: Primitive) -> TypeRef {
        let index: usize = typ.into();
        self.prim_ref_map[index]
    }

    pub fn associate_name_and_ref(&mut self, name: &str, idx: TypeRef) {
        if self.name_ref_map.contains_key(name) {
            panic!("data type redefinition: {name}");
        }
        self.name_ref_map.insert(name.to_string(), idx);
    }

    pub fn get_ctor_type(&self, ctor: &str) -> Option<TypeRef> {
        self.ctor_map.borrow().get(ctor).copied()
    }

    pub fn get_ctor_map(&self) -> Rc<RefCell<HashMap<String, TypeRef>>> {
        Rc::clone(&self.ctor_map)
    }

    pub fn get_ctor_index_and_field_type_ref_by_name(
        &self,
        typ: TypeRef,
        name: &str,
    ) -> (usize, Vec<TypeRef>) {
        match &self.types[typ] {
            Type::Enum { ctors, name: _ } => {
                let ctor_idx = ctors
                    .iter()
                    .position(|ctor| ctor.0 == name)
                    .unwrap_or_else(|| panic!("{name} not found"));
                let ctor = &ctors[ctor_idx];
                (ctor_idx, ctor.1.to_vec())
            }
            _ => panic!("can't get fields of non enum type"),
        }
    }

    pub fn get_type_ref_by_name(&self, name: &str) -> Option<TypeRef> {
        self.name_ref_map.get(name).copied()
    }
    pub fn array_type(&mut self, elem: TypeRef) -> TypeRef {
        let res = Type::Array(elem);
        self.insert_type_or_get(res)
    }

    pub fn tuple_type(&mut self, fields: Vec<TypeRef>) -> TypeRef {
        let res = Type::Tuple { fields };
        self.insert_type_or_get(res)
    }

    fn ctor_type(&mut self, typ: (TypeRef, Vec<TypeRef>)) -> TypeRef {
        self.callable_type(CallKind::Constructor, typ.0, typ.1)
    }

    pub fn enum_type(&mut self, ctors: Vec<(String, Vec<TypeRef>)>, name: String) -> TypeRef {
        let res = Type::Enum {
            ctors: ctors.clone(),
            name,
        };
        let enum_type = self.insert_type_or_get(res);
        for ctor in ctors.into_iter() {
            if self.ctor_map.borrow().contains_key(&ctor.0) {
                panic!("multiple definitions for constructor name `{}`", ctor.0);
            }
            let ctor_type = self.ctor_type((enum_type, ctor.1));
            self.ctor_map.borrow_mut().insert(ctor.0, ctor_type);
        }
        enum_type
    }

    pub fn opaque_name_type(&mut self, name: &str) -> TypeRef {
        let res = Type::Opaque {
            alias: Either::Right(name.to_string()),
        };
        self.insert_type_or_get(res)
    }

    pub fn opaque_type(&mut self, type_ref: TypeRef) -> TypeRef {
        let res = Type::Opaque {
            alias: Either::Left(type_ref),
        };
        self.insert_type_or_get(res)
    }

    pub fn reference_type(&mut self, type_ref: TypeRef) -> TypeRef {
        let res = Type::Reference {
            refer: Either::Left(type_ref),
        };
        self.insert_type_or_get(res)
    }

    pub fn callable_type(
        &mut self,
        kind: CallKind,
        ret_type: TypeRef,
        parameters: Vec<TypeRef>,
    ) -> TypeRef {
        let res = Type::Callable {
            kind,
            ret_type,
            parameters,
        };
        self.insert_type_or_get(res)
    }

    fn insert_type_or_get(&mut self, typ: Type) -> TypeRef {
        if let Some(typ) = self.type_ref_map.get(&typ) {
            return *typ;
        }

        let new_ref = self.types.insert(typ.clone());
        self.type_ref_map.insert(typ, new_ref);

        new_ref
    }

    fn add_primitive(&mut self, primitive: Primitive, name: Option<&str>) {
        let typ: Type = primitive.into();
        let prim_index: usize = primitive.into();

        let new_ref = self.types.insert(typ.clone());
        self.prim_ref_map[prim_index] = new_ref;

        self.type_ref_map.insert(typ, new_ref);
        if let Some(name) = name {
            self.name_ref_map.insert(name.to_string(), new_ref);
        }
    }

    fn add_primitives(&mut self) {
        TypeContext::PRIMITIVE_TYPE_NAME
            .iter()
            .enumerate()
            .for_each(|(idx, name)| {
                self.add_primitive(Primitive::try_from(idx).unwrap(), Some(name))
            });
    }

    pub fn refine_all_type(&mut self) {
        let mut refine_map: HashMap<TypeRef, TypeRef> = Default::default();
        for t in self.types.iter() {
            self.mark_to_be_refined_type(t.0, &mut refine_map);
        }

        // refine all types
        for (origin_type, target_type) in refine_map {
            self.refine_type(origin_type, Left(target_type));
        }

        // type has changed, we must update the map of type -> type_ref
        let mut new_node_map = HashMap::new();
        for &idx in self.type_ref_map.values() {
            new_node_map.insert(self.types[idx].clone(), idx);
        }
        self.type_ref_map = new_node_map;
    }

    fn refine_type(&mut self, t: TypeRef, target: Either<TypeRef, String>) {
        let typ = self.types.get_mut(t).unwrap();
        match typ {
            Type::Opaque { alias } => {
                *alias = target;
            }
            Type::Reference { refer } => {
                *refer = target;
            }
            _ => unreachable!(),
        }
    }

    fn mark_to_be_refined_type(&self, t: TypeRef, todo_map: &mut HashMap<TypeRef, TypeRef>) {
        let typ = self.types.get(t).unwrap();
        match typ {
            Type::Tuple { fields } => {
                for &field in fields {
                    self.mark_to_be_refined_type(field, todo_map);
                }
            }
            Type::Enum { ctors, name: _ } => {
                for ctor in ctors {
                    for &field in ctor.1.iter() {
                        self.mark_to_be_refined_type(field, todo_map);
                    }
                }
            }
            Type::Array(elem) => {
                self.mark_to_be_refined_type(*elem, todo_map);
            }
            Type::Primitive(_) => {}
            Type::Opaque { alias } => {
                if let Right(name) = alias {
                    let Some(&type_ref) = self.name_ref_map.get(name.as_str()) else {
                        panic!("unresolved type {name}");
                    };
                    todo_map.insert(t, type_ref);
                }
            }
            Type::Reference { refer } => {
                if let Right(name) = refer {
                    let Some(&type_ref) = self.name_ref_map.get(name.as_str()) else {
                        panic!("unresolved type {name}");
                    };
                    todo_map.insert(t, type_ref);
                }
            }
            Type::Callable {
                ret_type,
                parameters,
                kind: _,
            } => {
                self.mark_to_be_refined_type(*ret_type, todo_map);
                for &param in parameters {
                    self.mark_to_be_refined_type(param, todo_map);
                }
            }
        }
    }

    pub fn get_opaque_base_type(&self, typ: TypeRef) -> TypeRef {
        let mut typ = typ;
        loop {
            match self.types.get(typ).unwrap() {
                Type::Opaque { alias } => typ = *alias.as_ref().left().unwrap(),
                _ => return typ,
            }
        }
    }

    pub fn get_reference_base_type(&self, typ: TypeRef) -> Option<TypeRef> {
        match self.types.get(typ).unwrap() {
            Type::Reference { refer } => Some(*refer.as_ref().left().unwrap()),
            _ => None,
        }
    }

    pub fn is_t1_reference_of_t2(&self, t1: TypeRef, t2: TypeRef) -> bool {
        matches!(self.types.get(t1).unwrap(),
            Type::Reference { refer } if self.is_type_eq(*refer.as_ref().left().unwrap(), t2))
    }

    pub fn is_enum_type(&self, t: TypeRef) -> bool {
        matches!(self.get_type_by_ref(t), Type::Enum { ctors: _, name: _ })
    }

    pub fn is_tuple_type(&self, t: TypeRef) -> bool {
        matches!(self.get_type_by_ref(t), Type::Tuple { fields: _ })
    }

    // if true, both types have the same type id
    pub fn is_type_purely_eq(&self, t1: TypeRef, t2: TypeRef) -> bool {
        t1 == t2
    }

    // if true, both types represent the same nominal type
    pub fn is_type_opaque_eq(&self, t1: TypeRef, t2: TypeRef) -> bool {
        self.get_opaque_base_type(t1) == self.get_opaque_base_type(t2)
    }

    // if true, both types are reference type
    // and the referred types represent the same nominal type
    pub fn is_type_reference_eq(&self, t1: TypeRef, t2: TypeRef) -> bool {
        matches!((
            self.get_reference_base_type(self.get_opaque_base_type(t1)),
            self.get_reference_base_type(self.get_opaque_base_type(t2)),
        ), (Some(t1), Some(t2)) if self.is_type_opaque_eq(t1, t2))
    }

    // if true, both types represent the same nominal type
    pub fn is_type_eq(&self, t1: TypeRef, t2: TypeRef) -> bool {
        self.is_type_purely_eq(t1, t2)
            || self.is_type_opaque_eq(t1, t2)
            || self.is_type_reference_eq(t1, t2)
    }

    pub fn is_arithmetic_compatible(&self, t1: TypeRef, t2: TypeRef) -> bool {
        self.is_arithmetic_type(t1) && self.is_arithmetic_type(t2)
    }

    // if true, both types are compatible when doing assignment
    pub fn is_compatible(&self, t1: TypeRef, t2: TypeRef) -> bool {
        self.is_type_eq(t1, t2) // the same nominal type
            || self.is_arithmetic_compatible(t1, t2) // can be cast 
            || self.is_type_eq(t1, self.singleton_type(Primitive::Object)) // unsafe cast due to polymorphism
            || self.is_type_eq(t2, self.singleton_type(Primitive::Object)) // unsafe cast due to polymorphism
            || self.is_t1_reference_of_t2(t1, t2) // one is reference and the other is the referred type
            || self.is_t1_reference_of_t2(t2, t1)
    }

    pub fn is_callable_type(&self, t: TypeRef) -> bool {
        matches!(
            self.types.get(t).unwrap(),
            Type::Callable {
                ret_type: _,
                parameters: _,
                kind: _
            }
        )
    }

    pub fn is_array_type(&self, t: TypeRef) -> bool {
        matches!(self.types.get(t).unwrap(), Type::Array(_))
    }

    pub fn is_index_type(&self, t: TypeRef) -> bool {
        self.is_type_eq(t, self.singleton_type(Primitive::Int32))
    }

    pub fn is_arithmetic_type(&self, t: TypeRef) -> bool {
        self.is_type_eq(t, self.singleton_type(Primitive::Int32))
            || self.is_type_eq(t, self.singleton_type(Primitive::Float64))
    }

    pub fn is_boolean_testable_type(&self, t: TypeRef) -> bool {
        self.is_type_eq(t, self.singleton_type(Primitive::Bool))
    }

    pub fn is_partially_ordered_type(&self, t: TypeRef) -> bool {
        self.is_totally_ordered_type(t)
            || self.is_type_eq(t, self.singleton_type(Primitive::Float64))
    }

    pub fn is_partially_equal_type(&self, t: TypeRef) -> bool {
        self.is_totally_equal_type(t) || self.is_type_eq(t, self.singleton_type(Primitive::Float64))
    }

    pub fn is_totally_ordered_type(&self, t: TypeRef) -> bool {
        self.is_type_eq(t, self.singleton_type(Primitive::Int32))
    }

    pub fn is_totally_equal_type(&self, t: TypeRef) -> bool {
        self.is_type_eq(t, self.singleton_type(Primitive::Int32))
            || self.is_type_eq(t, self.singleton_type(Primitive::Bool))
            || self.is_type_eq(t, self.singleton_type(Primitive::Str))
    }

    pub fn mark_to_be_recovered_type(
        &self,
        t: TypeRef,
        display_name: &HashMap<TypeRef, String>,
        todo_map: &mut HashMap<TypeRef, String>,
    ) {
        let typ = self.types.get(t).unwrap();
        match typ {
            Type::Tuple { fields } => {
                for &field in fields {
                    self.mark_to_be_recovered_type(field, display_name, todo_map);
                }
            }
            Type::Enum { ctors, name: _ } => {
                for ctor in ctors {
                    for &field in ctor.1.iter() {
                        self.mark_to_be_recovered_type(field, display_name, todo_map);
                    }
                }
            }
            Type::Array(elem) => {
                self.mark_to_be_recovered_type(*elem, display_name, todo_map);
            }
            Type::Primitive(_) => {}
            Type::Opaque { alias } => {
                if let Left(typ) = alias {
                    let name = display_name.get(typ).unwrap();
                    todo_map.insert(t, name.clone());
                }
            }
            Type::Reference { refer } => {
                if let Left(typ) = refer {
                    let name = display_name.get(typ).unwrap();
                    todo_map.insert(t, name.clone());
                }
            }
            Type::Callable {
                ret_type,
                parameters,
                kind: _,
            } => {
                self.mark_to_be_recovered_type(*ret_type, display_name, todo_map);
                for &param in parameters {
                    self.mark_to_be_recovered_type(param, display_name, todo_map);
                }
            }
        }
    }

    pub fn get_display_name_map(&self) -> (Self, HashMap<TypeRef, String>) {
        let mut context = self.clone();
        let mut display_name_map = HashMap::new();
        let mut namer = UniqueName::new();
        let mut todo_map: HashMap<_, _> = Default::default();

        for (k, v) in context.name_ref_map.iter() {
            display_name_map.insert(*v, k.clone());
        }

        for (type_ref, _) in context.types.iter() {
            display_name_map
                .entry(type_ref)
                .or_insert_with(|| namer.next_name("anonymous_type"));
        }

        for (type_ref, _) in context.types.iter() {
            context.mark_to_be_recovered_type(type_ref, &display_name_map, &mut todo_map);
        }

        for (type_ref, name) in todo_map {
            context.refine_type(type_ref, Right(name))
        }

        let mut new_node_map = HashMap::new();
        for &idx in context.type_ref_map.values() {
            new_node_map.insert(context.types[idx].clone(), idx);
        }
        context.type_ref_map = new_node_map;

        (context, display_name_map)
    }

    fn display_type(&self, t: &Type, f: &mut String) -> std::fmt::Result {
        match t {
            Type::Tuple { fields } => {
                write!(f, "(")?;
                for (idx, &field) in fields.iter().enumerate() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    self.display_type_ref(field, f)?
                }
                write!(f, ")")
            }
            Type::Enum { ctors, name: _ } => {
                write!(f, "{{")?;
                for (idx, ctor) in ctors.iter().enumerate() {
                    if idx != 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "<{} ", ctor.0)?;
                    self.display_type(
                        &Type::Tuple {
                            fields: ctor.1.clone(),
                        },
                        f,
                    )?;
                    write!(f, ">")?;
                }
                write!(f, "}}")
            }
            Type::Primitive(p) => write!(f, "{p}"),
            Type::Opaque { alias } => {
                write!(f, "{}", alias.as_ref().right().unwrap())
            }
            Type::Reference { refer } => {
                write!(f, "ref {}", refer.as_ref().right().unwrap())
            }
            Type::Array(arr) => {
                write!(f, "[")?;
                self.display_type_ref(*arr, f)?;
                write!(f, "]")
            }
            Type::Callable {
                ret_type,
                parameters,
                kind: _,
            } => {
                self.display_type(
                    &Type::Tuple {
                        fields: parameters.clone(),
                    },
                    f,
                )?;

                write!(f, " -> ",)?;
                self.display_type_ref(*ret_type, f)
            }
        }
    }

    fn display_type_ref(&self, t: TypeRef, f: &mut String) -> std::fmt::Result {
        let t = self.types.get(t).unwrap();
        self.display_type(t, f)
    }

    pub fn get_type_ref_string(&self, t: TypeRef) -> String {
        let mut s = "".to_string();
        self.display_type_ref(t, &mut s).unwrap();
        s
    }
}

impl Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let idx: usize = (*self).into();
        write!(f, "{}", TypeContext::PRIMITIVE_TYPE_NAME[idx])
    }
}

impl Display for TypeContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (context, map) = self.get_display_name_map();
        dbg!(&context);
        writeln!(f, "TypeContext {{")?;
        for (key, typ) in context.types.iter() {
            let mut s = "".to_string();
            self.display_type(typ, &mut s)?;
            writeln!(f, "    {}: {s}", map.get(&key).unwrap())?;
        }
        writeln!(f, "}}")
    }
}

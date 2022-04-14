use either::Either;
use std::{
    collections::{HashMap, HashSet},
    panic,
    rc::Rc,
    vec,
};
use Either::{Left, Right};

use crate::{
    ast::NameTypeBind,
    sym::{self, SymbolTable},
};

use self::unique_name::UniqueName;

mod unique_name;

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
    Primitive(Box<Primitive>),
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
        Type::Primitive(Box::new(x))
    }
}

impl From<Opaque> for Type {
    fn from(x: Opaque) -> Self {
        Type::Opaque(x)
    }
}

#[derive(Debug, Default)]
pub struct Module {
    pub data_defs: Vec<DataDef>,
    pub func_defs: Vec<FuncDef>,
}

#[derive(Debug)]
pub struct RefPath {
    pub items: Vec<String>,
}

#[derive(Debug)]
pub struct DataDef {
    pub name: String,
    pub con_list: Type,
}

#[derive(Debug, Default)]
pub struct FuncDef {
    pub name: String,
    pub param_def: Vec<(bool, Rc<VarDef>)>,
    pub var_def: Vec<Rc<VarDef>>,
    pub tmp_def: Vec<Rc<VarDef>>,
    pub ret_def: Option<Rc<VarDef>>,
    pub blocks: Vec<Rc<Block>>,
}

#[derive(Debug)]
pub struct VarDef {
    pub name: String,
    pub typ: Type,
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

#[derive(Debug, Default)]
pub struct Stmt {
    pub left: Option<Rc<VarDef>>,
    pub right: Option<Value>,
    pub note: String,
}

#[derive(Debug)]
pub enum Terminator {
    Cond(Box<Value>, Rc<Block>, Rc<Block>),
    Select(Box<Value>, Vec<Rc<Block>>),
    Jump(Rc<Block>),
    Return,
}

#[derive(Debug)]
pub enum BinOp {
    Plus,
    Sub,
    Mult,
    Div,
    Mod,
}

#[derive(Debug)]
pub enum Value {
    Call(RefPath, Box<Value>, Box<Value>),
    Op(BinOp, Box<Value>, Box<Value>),
    Imm(Literal),
    Intrinsic(String, Vec<Box<Value>>),
    VarRef(Rc<VarDef>),
}

#[derive(Debug)]
pub enum Literal {
    Int(i32),
    Str(String),
    Bool(bool),
}

impl From<&crate::ast::Literal> for Literal {
    fn from(lit: &crate::ast::Literal) -> Self {
        match lit {
            crate::ast::Literal::Int(i) => Literal::Int(i.clone()),
            crate::ast::Literal::Str(s) => Literal::Str(s.clone()),
            crate::ast::Literal::Bool(b) => Literal::Bool(b.clone()),
        }
    }
}

#[derive(Debug, Default)]
struct MiddleIR {
    name_typeid_map: HashMap<String, usize>,
    type_typeid_map: HashMap<Type, usize>,
    types: Vec<Type>,
    unit: usize,
    bool: usize,
    str: usize,
    i32: usize,
    imports: HashMap<String, RefPath>,
    constructors: HashSet<String>,
    module: Module,
    position: Option<Rc<Block>>,
}

type SymTable<T> = Vec<HashMap<String, T>>;

impl MiddleIR {
    fn insert_type_or_get(&mut self, typ: Type) -> (usize, Type) {
        if self.type_typeid_map.contains_key(&typ) {
            return (*self.type_typeid_map.get(&typ).unwrap(), typ);
        }

        let self_index = self.types.len();
        self.types.push(typ.clone());
        self.type_typeid_map.insert(typ.clone(), self_index);

        (self_index, typ)
    }

    fn resolve_type_with_at(&mut self, ast_type: &crate::ast::Type) -> (usize, Type) {
        let (idx, _typ) = self.resolve_type(ast_type, false);

        let opaque: Type = Opaque {
            refer: Either::Left(idx),
        }
        .into();

        self.insert_type_or_get(opaque)
    }

    fn resolve_type(&mut self, ast_type: &crate::ast::Type, allow_opaque: bool) -> (usize, Type) {
        match ast_type {
            crate::ast::Type::Arrow(_, _) => unimplemented!(),

            crate::ast::Type::Tuple(tuple) => {
                let mut fields = vec![];
                let mut indices = vec![];
                for ty in tuple {
                    let (index, field) = self.resolve_type(ty, allow_opaque);
                    indices.push(index);
                    fields.push(field);
                }

                let res: Type = Tuple { fields }.into();
                let (self_index, res) = self.insert_type_or_get(res);

                (self_index, res)
            }

            crate::ast::Type::Enum(e) => {
                let mut enu = Enum {
                    constructors: Default::default(),
                };
                let mut ctors = vec![];
                let mut indices = vec![];

                for crate::ast::ConstructorType { name, inner } in e {
                    let ty = if inner.is_some() {
                        let (index, ty) = self.resolve_type(inner.as_ref().unwrap(), allow_opaque);
                        indices.push(index);
                        Some(ty)
                    } else {
                        None
                    };
                    ctors.push((name.clone(), ty));
                }

                enu.constructors = ctors;

                let res: Type = enu.into();
                self.insert_type_or_get(res)
            }

            crate::ast::Type::Unit => (self.unit, self.types[self.unit].clone()),

            crate::ast::Type::Named(s) => {
                if self.name_typeid_map.contains_key(s) {
                    let idx = *self.name_typeid_map.get(s).unwrap();
                    (idx, self.types[idx].clone())
                } else if allow_opaque {
                    let opaque: Type = Opaque {
                        refer: Either::Right(s.to_string()),
                    }
                    .into();

                    self.insert_type_or_get(opaque)
                } else {
                    panic!("unresolved type: {}", s);
                }
            }
        }
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

        self.bool = bi;
        self.i32 = ii;
        self.unit = ui;
        self.str = si;
    }

    fn resolve_all_type(&mut self, module: &crate::ast::Module) {
        for crate::ast::DataDef { name, con_list } in &module.data_defs {
            if self.name_typeid_map.contains_key(name) {
                panic!("data type redefinition: {}", name);
            }
            let (idx, _typ) = self.resolve_type(con_list, true);
            self.name_typeid_map.insert(name.to_string(), idx);
        }
    }

    fn resolve_opaque_type(name_map: &HashMap<String, usize>, t: &mut Type) {
        match t {
            Type::Tuple(tuple) => {
                let Tuple { fields } = tuple.as_mut();
                for field in fields {
                    MiddleIR::resolve_opaque_type(name_map, field);
                }
            }
            Type::Enum(enu) => {
                let Enum { constructors } = enu.as_mut();
                for ctor in constructors {
                    for field in &mut ctor.1 {
                        MiddleIR::resolve_opaque_type(name_map, field);
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

    fn resolve_all_opaque_type(&mut self) {
        for t in self.types.iter_mut() {
            MiddleIR::resolve_opaque_type(&self.name_typeid_map, t)
        }
        let mut new_node_map = HashMap::new();
        for idx in self.type_typeid_map.values() {
            new_node_map.insert(self.types[*idx].clone(), *idx);
        }
        self.type_typeid_map = new_node_map;
    }

    fn resolve_import(&mut self, module: &crate::ast::Module) {
        let imports = &module.imports;
        for import in imports {
            let items = import.items.clone();
            let path = RefPath { items };
            let name = path.items.last().expect("empty import").clone();
            if self.imports.contains_key(&name) {
                panic!(
                    "conflict import: {} and {}",
                    path.items.join("."),
                    self.imports.get(&name).unwrap().items.join(".")
                )
            }
            self.imports.insert(name, path);
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

    fn collect_all_constructor(&mut self) {
        for ty in self.types.iter() {
            MiddleIR::collect_constructor(&mut self.constructors, ty)
        }
    }

    fn convert_asgn(
        &mut self,
        name: &str,
        expr: &crate::ast::Expr,
        table: &mut SymTable<Rc<VarDef>>,
    ) {
        self.convert_expr(expr, table, Some(name));
    }

    fn convert_construction(&mut self) -> Value {
        todo!()
    }

    fn convert_expr(
        &mut self,
        expr: &crate::ast::Expr,
        table: &mut SymTable<Rc<VarDef>>,
        out: Option<&str>,
    ) {
        let cur_bb = self.position.as_ref().expect("must set the insert point");
        let mut stmt = Stmt::default();

        if let Some(name) = out {
            let var = table.find_symbol(name).expect("variable not defined");
            stmt.left = Some(Rc::clone(var));
        }
        
        stmt.right = Some(match expr {
            crate::ast::Expr::MatchExpr(_) => todo!(),
            crate::ast::Expr::BraExpr(_) => todo!(),
            crate::ast::Expr::CallExpr(_) => todo!(),
            crate::ast::Expr::ArithExpr(_) => todo!(),
            crate::ast::Expr::Var(name) => {
                if self.constructors.contains(name) {
                    self.convert_construction()
                } else {
                    Value::VarRef(Rc::clone(
                        table.find_symbol(name).expect("variable not defined"),
                    ))
                }
            }
            crate::ast::Expr::Lit(lit) => Value::Imm(lit.into()),
        });
    }

    fn convert_let(
        &mut self,
        stmt: &crate::ast::LetStmt,
        namer: &mut UniqueName,
        table: &mut SymTable<Rc<VarDef>>,
        def: &mut FuncDef,
    ) {
        let crate::ast::LetStmt {
            var_name,
            typ,
            expr,
        } = stmt;

        let name = namer.next_name(var_name);
        let (_, typ) = self.resolve_type(typ, false);
        let new_var = Rc::new(VarDef { name, typ });

        table.insert_symbol(var_name.clone(), Rc::clone(&new_var));
        def.tmp_def.push(new_var);

        self.convert_asgn(var_name, expr, table);
    }

    fn convert_stmt(
        &mut self,
        stmt: &crate::ast::Stmt,
        namer: &mut UniqueName,
        table: &mut SymTable<Rc<VarDef>>,
        def: &mut FuncDef,
    ) {
        match stmt {
            crate::ast::Stmt::Let(stmt) => self.convert_let(stmt, namer, table, def),
            crate::ast::Stmt::Asgn(stmt) => self.convert_asgn(&stmt.var_name, &stmt.expr, table),
            crate::ast::Stmt::Expr(stmt) => self.convert_expr(stmt, table, None),
        }
    }

    fn convert_bracket_body(
        &mut self,
        body: &crate::ast::BracketBody,
        namer: &mut UniqueName,
        table: &mut SymTable<Rc<VarDef>>,
        def: &mut FuncDef,
        out: Option<&str>,
    ) {
        for stmt in &body.stmts {
            self.convert_stmt(stmt, namer, table, def)
        }
        if let Some(ret_expr) = &body.ret_expr {
            self.convert_expr(ret_expr, table, out);
        }
    }

    fn convert_fn_definition(&mut self, func: &crate::ast::FuncDef) -> FuncDef {
        let mut def = FuncDef {
            name: func.name.clone(),
            ..Default::default()
        };

        // setup the return type and create the return value variable
        let (_, typ) = self.resolve_type(&func.ret_type, false);
        let name = "#ret.ptr".to_string();
        let name_cpy = name.clone();
        let ret = Rc::new(VarDef { name, typ });
        def.ret_def = Some(ret.clone());

        // setup the symbol table
        // insert the return value variable
        let mut sym_table: SymTable<Rc<VarDef>> = SymTable::new();
        sym_table.entry();
        sym_table.insert_symbol(name_cpy, Rc::clone(&ret));

        // initialize all parameters
        for NameTypeBind {
            with_at,
            var_name,
            typ,
        } in &func.param_list
        {
            let (_, typ) = if *with_at {
                self.resolve_type(typ, false)
            } else {
                self.resolve_type_with_at(typ)
            };
            let name = format!("#{}", var_name);
            let name_cpy = name.clone();
            let param = Rc::new(VarDef { name, typ });

            // insert the parameter into symbol table
            sym_table.insert_symbol(name_cpy, Rc::clone(&param));
            def.param_def.push((*with_at, param));
        }

        // return block
        let ret_block = Rc::new(Block {
            terminator: Terminator::Return,
            stmts: vec![],
        });

        // add an empty entry block and set the insert point
        let entry_block = Rc::new(Block {
            terminator: Terminator::Jump(Rc::clone(&ret_block)),
            stmts: vec![],
        });
        self.position = Some(Rc::clone(&entry_block));

        def.blocks.push(entry_block);

        // convert the function body
        let mut namer = UniqueName::new();
        self.convert_bracket_body(
            &func.body,
            &mut namer,
            &mut sym_table,
            &mut def,
            Some("#ret.ptr"),
        );

        def.blocks.push(ret_block);

        // exit the symbol table scope
        sym_table.exit();
        def
    }

    fn convert_ast(&mut self, module: &crate::ast::Module) {
        for fun in &module.func_defs {
            let new_def = self.convert_fn_definition(fun);
            self.module.func_defs.push(new_def);
        }
    }

    pub fn create_from_ast(module: &crate::ast::Module) -> Self {
        let mut mir = MiddleIR::default();

        mir.add_primitive();
        mir.resolve_all_type(module);
        mir.resolve_all_opaque_type();
        mir.resolve_import(module);
        mir.collect_all_constructor();
        mir.convert_ast(module);

        mir
    }
}

impl From<crate::ast::Module> for MiddleIR {
    fn from(module: crate::ast::Module) -> Self {
        MiddleIR::create_from_ast(&module)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;
    use std::fs;

    #[test]
    fn test_codegen() {
        let s = fs::read_to_string("../example/stage1/adt.mag").expect("read file fail");
        let ast = frontend::parse(&s);
        let mir: MiddleIR = ast.into();
        println!("{:#?}", mir);
    }
}

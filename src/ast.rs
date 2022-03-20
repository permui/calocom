
#[derive(Debug)]
pub struct Module { // the highest level entity: a file ~ a module
    pub imports: Vec<RefPath>,
    pub data_defs: Vec<DataDef>,
    pub func_defs: Vec<FuncDef>
}

#[derive(Debug)]
pub struct RefPath {
    pub items: Vec<String>
}

#[derive(Debug)]
pub struct DataDef {
    pub name: String,
    pub con_list: Type,
}

#[derive(Debug)]
pub struct ConstructorType {
    pub name: String,
    pub inner: Option<Type>
}

#[derive(Debug)]
pub struct ConstructorVar {
    pub name: String,
    pub inner: Option<String>
}

#[derive(Debug)]
pub enum Type {
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Enum(Vec<ConstructorType>),
    Unit,
    Named(String)
}

#[derive(Debug)]
pub struct FuncDef {
    pub name: String,
    pub param_list: Vec<NameTypeBind>,
    pub ret_type: Type,
    pub body: Box<BracketBody>
}

#[derive(Debug)]
pub struct NameTypeBind {
    pub with_at: bool,
    pub var_name: String,
    pub typ: Type
}

#[derive(Debug)]
pub struct BracketBody {
    pub stmts: Vec<Stmt>,
    pub ret_expr: Option<Box<Expr>>
}

#[derive(Debug)]
pub struct LetStmt {
    pub var_name: String,
    pub typ: Type,
    pub expr: Box<Expr>
}

#[derive(Debug)]
pub struct AsgnStmt {
    pub var_name: String,
    pub expr: Box<Expr>
}

#[derive(Debug)]
pub enum Stmt {
    Let(Box<LetStmt>),
    Asgn(Box<AsgnStmt>),
    Expr(Box<Expr>)
}

#[derive(Debug)]
pub struct CallExpr {
    pub path: RefPath,
    pub gen: Option<Type>, // generic notation
    pub args: Vec<Argument>
}

#[derive(Debug)]
pub struct ArithExpr {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: BinOp
}

#[derive(Debug)]
pub struct MatchExpr {
    pub e: Box<Expr>,
    pub arms: Vec<(Pattern, Box<Expr>)>
}

#[derive(Debug)]
pub enum Expr {
    BraExpr(BracketBody),
    CallExpr(CallExpr),
    ArithExpr(ArithExpr),
    MatchExpr(MatchExpr),
    Var(String),
    Lit(Literal)
}

#[derive(Debug)]
pub enum Argument {
    Expr(Expr),
    AtVar(String)
}

#[derive(Debug)]
pub enum BinOp {
    Plus,
    Sub,
    Mult,
    Div,
    Mod
}


#[derive(Debug)]
pub enum Pattern {
    Lit(Literal),
    Con(ConstructorVar)
}

#[derive(Debug)]
pub enum Literal {
    Int(i32),
    Str(String),
    Bool(bool)
}


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
    pub inner: Vec<Type>
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
    Array(Box<Type>),
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
pub struct WhileStmt {
    pub condition: Box<Expr>,
    pub body: Box<BracketBody>
}

// for range is [range_l, range_r)
#[derive(Debug)]
pub struct ForStmt {
    pub var_name: String,
    pub range_l: Box<Expr>,
    pub range_r: Box<Expr>,
    pub body: Box<BracketBody>
}

// now left-hand-side can be an expression
// like `a[3] = 4;`
#[derive(Debug)]
pub struct AsgnStmt {
    pub lexp: Box<Expr>,
    pub rexp: Box<Expr>
}

#[derive(Debug)]
pub enum Stmt {
    Let(Box<LetStmt>),
    While(Box<WhileStmt>),
    For(Box<ForStmt>),
    Return,
    Break,
    Continue,
    Asgn(Box<AsgnStmt>),
    Expr(Box<Expr>)
}

#[derive(Debug)]
pub struct ClosureExpr {
    pub param_list: Vec<NameTypeBind>,
    pub ret_type: Box<Type>,
    pub body: Box<Expr>
}

#[derive(Debug)]
pub struct CallExpr {
    pub func: Box<Expr>, // function may be a closure expression
    pub gen: Option<Type>, // generic notation
    pub args: Vec<Argument>
}


#[derive(Debug)]
pub struct MatchExpr {
    pub e: Box<Expr>,
    pub arms: Vec<(Pattern, Box<Expr>)>
}

#[derive(Debug)]
pub struct IfExpr {
    pub condition: Box<Expr>,
    pub t_branch: Box<Expr>, // true branch
    pub f_branch: Option<Box<Expr>> // false branch (that is, else, may be not present)
}

#[derive(Debug)]
pub enum BinOp {
    Or,
    And,

    Le,
    Ge,
    Eq,
    Ne,
    Lt,
    Gt,

    Plus,
    Sub,
    Mult,
    Div,
    Mod
}

#[derive(Debug)]
pub struct BinOperExpr {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: BinOp
}

#[derive(Debug)]
pub enum UnaOp {
    Not,

    Positive,
    Negative
}

#[derive(Debug)]
pub struct UnaOperExpr {
    pub x: Box<Expr>,
    pub op: UnaOp
}

#[derive(Debug)]
pub struct SubscriptExpr {
    pub arr: Box<Expr>,
    pub index: Box<Expr>
}

#[derive(Debug)]
pub enum Expr {
    Closure(ClosureExpr),
    Match(MatchExpr),
    If(IfExpr),

    BinOper(BinOperExpr),
    UnaOper(UnaOperExpr),

    Subscript(SubscriptExpr),
    
    CallExpr(CallExpr),

    Tuple(Vec<Expr>),

    Lit(Literal),
    Path(RefPath),

    UnitVal,

    BraExpr(BracketBody),
}

#[derive(Debug)]
pub enum Argument {
    Expr(Expr),
    AtVar(String)
}


/*
    data A = B(i32, (str, f64)) | C ;
    match a {
        /// here is a constructor pattern
        B(x, (y, z)) => ...  
        ...
    }
*/
#[derive(Debug)]
pub struct ConPattern {
    pub con_name: String,
    pub inner: Vec<Pattern>
}

#[derive(Debug)]
pub enum Pattern {
    Con(ConPattern),
    Tuple(Vec<Pattern>),
    Wildcard,
    Literal(Literal),
}

#[derive(Debug)]
pub enum Literal {
    Float(f64),
    Int(i32),
    Str(String),
    Bool(bool),
    Char(char)
}

use std::{fmt, collections::HashMap, hash::{Hash, Hasher}};

use crate::lexer::token::Token;

pub trait Node: fmt::Display {
    fn token_literal(&self) -> String;
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Program {
    pub stmts: Vec<Stmt>,
}

impl Program {
    pub fn new() -> Self {
        Self {
            stmts: Vec::new(),
        }
    }
}

impl Node for Program {
    fn token_literal(&self) -> String {
        match self.stmts.get(0) {
            Some(s) => s.token_literal(),
            None => String::new(),
        }
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            write!(f, "{}", stmt)?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum MNode {
    Prog(Program),
    Stmt(Stmt),
    Expr(Expr),
}

impl fmt::Display for MNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MNode::Prog(x) => write!(f, "{}", x),
            MNode::Stmt(x) => write!(f, "{}", x),
            MNode::Expr(x) => write!(f, "{}", x),
        }
    }
}

// ============================================================================
// Statements
// ============================================================================

pub trait Statement: Node {
    fn stmt_node(&self);
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expr,
}

impl Node for LetStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Statement for LetStatement {
    fn stmt_node(&self) {
    }
}

impl fmt::Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} = {};", self.token.literal, self.name, self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ReturnStatement {
    pub token: Token,
    pub retval: Expr,
}

impl Node for ReturnStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Statement for ReturnStatement {
    fn stmt_node(&self) {
    }
}

impl fmt::Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", self.token.literal, self.retval)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BlockStatement {
    pub token: Token,
    pub stmts: Vec<Stmt>,
}

impl Node for BlockStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Statement for BlockStatement {
    fn stmt_node(&self) {
    }
}

impl fmt::Display for BlockStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            write!(f, "{}", stmt)?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expr: Expr,
}

impl Node for ExpressionStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Statement for ExpressionStatement {
    fn stmt_node(&self) {
    }
}

impl fmt::Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Stmt {
    Let(LetStatement),
    Return(ReturnStatement),
    Block(BlockStatement),
    Expression(ExpressionStatement),
}

impl Node for Stmt {
    fn token_literal(&self) -> String {
        match self {
            Stmt::Let(x) => x.token_literal(),
            Stmt::Return(x) => x.token_literal(),
            Stmt::Block(x) => x.token_literal(),
            Stmt::Expression(x) => x.token_literal(),
        }
    }
}

impl Statement for Stmt {
    fn stmt_node(&self) {
        match self {
            Stmt::Let(x) => x.stmt_node(),
            Stmt::Return(x) => x.stmt_node(),
            Stmt::Block(x) => x.stmt_node(),
            Stmt::Expression(x) => x.stmt_node(),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Let(x) => write!(f, "{}", x),
            Stmt::Return(x) => write!(f, "{}", x),
            Stmt::Block(x) => write!(f, "{}", x),
            Stmt::Expression(x) => write!(f, "{}", x),
        }
    }
}

// ============================================================================
// Expressions
// ============================================================================

pub trait Expression: Node {
    fn expr_node(&self);
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Identifier {
    pub token: Token,
    pub value: String,
}

impl Node for Identifier {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for Identifier {
    fn expr_node(&self) {
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: i128,
}

impl Node for IntegerLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for IntegerLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for IntegerLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BooleanLiteral {
    pub token: Token,
    pub value: bool,
}

impl Node for BooleanLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for BooleanLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for BooleanLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct StringLiteral {
    pub token: Token,
    pub value: String,
}

impl Node for StringLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for StringLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for StringLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ArrayLiteral {
    pub token: Token,
    pub elements: Vec<Expr>,
}

impl Node for ArrayLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for ArrayLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for ArrayLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        write!(
            f,
            "{}",
            self.elements.iter()
                .map(|p| format!("{}", p))
                .collect::<Vec<String>>()
                .join(", ")
        )?;
        write!(f, "]")
    }
}

#[derive(Clone, Debug)]
pub struct HashLiteral {
    pub token: Token,
    pub pairs: HashMap<Expr, Expr>,
}

impl Hash for HashLiteral {
    fn hash<H: Hasher>(&self, _state: &mut H) {
    }
}

impl PartialEq for HashLiteral {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl Eq for HashLiteral {}

impl Node for HashLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for HashLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for HashLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        write!(
            f,
            "{}",
            self.pairs.iter()
                .map(|(k, v)| format!("{}: {}", k, v))
                .collect::<Vec<String>>()
                .join(", ")
        )?;
        write!(f, "}}")
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expr>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl Node for IfExpression {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for IfExpression {
    fn expr_node(&self) {
    }
}

impl fmt::Display for IfExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "if {} {}", self.condition, self.consequence)?;
        if let Some(a) = &self.alternative {
            write!(f, "else {}", a)?;
        };
        Ok(())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Prefix {
    pub token: Token,
    pub operator: String,
    pub right: Box<Expr>,
}

impl Node for Prefix {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for Prefix {
    fn expr_node(&self) {
    }
}

impl fmt::Display for Prefix {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}{})", self.operator, self.right)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Infix {
    pub token: Token,
    pub left: Box<Expr>,
    pub operator: String,
    pub right: Box<Expr>,
}

impl Node for Infix {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for Infix {
    fn expr_node(&self) {
    }
}

impl fmt::Display for Infix {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.operator, self.right)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FnLiteral {
    pub token: Token,
    pub params: Vec<Identifier>,
    pub body: BlockStatement,
}

impl Node for FnLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for FnLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for FnLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.token_literal())?;
        write!(
            f,
            "{}",
            self.params.iter().map(|p| format!("{}", p)).collect::<Vec<String>>().join(", ")
        )?;
        write!(f, ") {}", self.body)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FnCall {
    pub token: Token,
    pub function: Box<Expr>,
    pub args: Vec<Expr>,
}

impl Node for FnCall {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for FnCall {
    fn expr_node(&self) {
    }
}

impl fmt::Display for FnCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.function)?;
        write!(
            f,
            "{})",
            self.args.iter().map(|p| format!("{}", p)).collect::<Vec<String>>().join(", ")
        )
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct IndexOperation {
    pub token: Token,
    pub left: Box<Expr>,
    pub index: Box<Expr>,
}

impl Node for IndexOperation {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for IndexOperation {
    fn expr_node(&self) {
    }
}

impl fmt::Display for IndexOperation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Expr {
    Ident(Identifier),
    Int(IntegerLiteral),
    Bool(BooleanLiteral),
    Str(StringLiteral),
    Array(ArrayLiteral),
    Hash(HashLiteral),
    Pre(Prefix),
    In(Infix),
    If(IfExpression),
    Fn(FnLiteral),
    Call(FnCall),
    Index(IndexOperation),
}

impl Node for Expr {
    fn token_literal(&self) -> String {
        match self {
            Expr::Ident(x) => x.token_literal(),
            Expr::Int(x) => x.token_literal(),
            Expr::Bool(x) => x.token_literal(),
            Expr::Str(x) => x.token_literal(),
            Expr::Array(x) => x.token_literal(),
            Expr::Hash(x) => x.token_literal(),
            Expr::Pre(x) => x.token_literal(),
            Expr::In(x) => x.token_literal(),
            Expr::If(x) => x.token_literal(),
            Expr::Fn(x) => x.token_literal(),
            Expr::Call(x) => x.token_literal(),
            Expr::Index(x) => x.token_literal(),
        }
    }
}

impl Expression for Expr {
    fn expr_node(&self) {
        match self {
            Expr::Ident(x) => x.expr_node(),
            Expr::Int(x) => x.expr_node(),
            Expr::Bool(x) => x.expr_node(),
            Expr::Str(x) => x.expr_node(),
            Expr::Array(x) => x.expr_node(),
            Expr::Hash(x) => x.expr_node(),
            Expr::Pre(x) => x.expr_node(),
            Expr::In(x) => x.expr_node(),
            Expr::If(x) => x.expr_node(),
            Expr::Fn(x) => x.expr_node(),
            Expr::Call(x) => x.expr_node(),
            Expr::Index(x) => x.expr_node(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Ident(x) => write!(f, "{}", x),
            Expr::Int(x) => write!(f, "{}", x),
            Expr::Bool(x) => write!(f, "{}", x),
            Expr::Str(x) => write!(f, "{}", x),
            Expr::Array(x) => write!(f, "{}", x),
            Expr::Hash(x) => write!(f, "{}", x),
            Expr::Pre(x) => write!(f, "{}", x),
            Expr::In(x) => write!(f, "{}", x),
            Expr::If(x) => write!(f, "{}", x),
            Expr::Fn(x) => write!(f, "{}", x),
            Expr::Call(x) => write!(f, "{}", x),
            Expr::Index(x) => write!(f, "{}", x),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::token_type::TokenType;

    #[test]
    fn test_fmt_display() {
        let mut program = Program::new();

        program.stmts.push(Stmt::Let(LetStatement {
            token: Token { token_type: TokenType::LET, literal: "let".to_string() },
            name: Identifier {
                token: Token { token_type: TokenType::IDENT, literal: "myVar".to_string() },
                value: "myVar".to_string(),
            },
            value: Expr::Ident(Identifier {
                token: Token { token_type: TokenType::IDENT, literal: "anotherVar".to_string() },
                value: "anotherVar".to_string(),
            }),
        }));

        assert_eq!("let myVar = anotherVar;", format!("{}", program));
    }
}

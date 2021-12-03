use crate::lexer::token::Token;

pub trait Node {
    fn token_literal(&self) -> String;
}

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

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Stmt {
    Let(LetStatement),
}

impl Node for Stmt {
    fn token_literal(&self) -> String {
        match self {
            Stmt::Let(x) => x.token_literal(),
        }
    }
}

impl Statement for Stmt {
    fn stmt_node(&self) {
        match self {
            Stmt::Let(x) => x.stmt_node(),
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

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Expr {
    Ident(Identifier),
}

impl Node for Expr {
    fn token_literal(&self) -> String {
        match self {
            Expr::Ident(x) => x.token_literal(),
        }
    }
}

impl Expression for Expr {
    fn expr_node(&self) {
        match self {
            Expr::Ident(x) => x.expr_node(),
        }
    }
}

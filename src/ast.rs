use std::fmt;

use crate::lexer::token::Token;

pub trait Node: fmt::Display {
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

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            write!(f, "{}", stmt)?;
        }
        Ok(())
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
    Expression(ExpressionStatement),
}

impl Node for Stmt {
    fn token_literal(&self) -> String {
        match self {
            Stmt::Let(x) => x.token_literal(),
            Stmt::Return(x) => x.token_literal(),
            Stmt::Expression(x) => x.token_literal(),
        }
    }
}

impl Statement for Stmt {
    fn stmt_node(&self) {
        match self {
            Stmt::Let(x) => x.stmt_node(),
            Stmt::Return(x) => x.stmt_node(),
            Stmt::Expression(x) => x.stmt_node(),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Let(x) => write!(f, "{}", x),
            Stmt::Return(x) => write!(f, "{}", x),
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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Ident(x) => write!(f, "{}", x),
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
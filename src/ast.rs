use std::{fmt, collections::HashMap, hash::{Hash, Hasher}};

use crate::{lexer::token::Token, interpreter::environment::Environment};

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
        write!(f, "\"{}\"", self.value)
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct HashLiteral {
    pub token: Token,
    pub pairs: HashMap<Expr, Expr>,
}

impl Hash for HashLiteral {
    fn hash<H: Hasher>(&self, _state: &mut H) {
    }
}

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
        write!(f, "if {} {{ {} }}", self.condition, self.consequence)?;
        if let Some(a) = &self.alternative {
            write!(f, " else {{ {} }}", a)?;
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
    pub name: Option<String>,
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
        if self.name.is_some() {
            write!(f, "<{}>", self.name.as_ref().unwrap())?;
        };
        write!(
            f,
            "{}",
            self.params.iter().map(|p| format!("{}", p)).collect::<Vec<String>>().join(", ")
        )?;
        write!(f, ") {{ {} }}", self.body)
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
pub struct MacroLiteral {
    pub token: Token,
    pub params: Vec<Identifier>,
    pub body: BlockStatement,
}

impl Node for MacroLiteral {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl Expression for MacroLiteral {
    fn expr_node(&self) {
    }
}

impl fmt::Display for MacroLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "macro({}) {{\n{}\n}}",
            self.params
                .iter()
                .map(|p| format!("{}", p))
                .collect::<Vec<String>>()
                .join(", "),
            self.body,
        )
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
    Macro(MacroLiteral),
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
            Expr::Macro(x) => x.token_literal(),
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
            Expr::Macro(x) => x.expr_node(),
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
            Expr::Macro(x) => write!(f, "{}", x),
            Expr::Pre(x) => write!(f, "{}", x),
            Expr::In(x) => write!(f, "{}", x),
            Expr::If(x) => write!(f, "{}", x),
            Expr::Fn(x) => write!(f, "{}", x),
            Expr::Call(x) => write!(f, "{}", x),
            Expr::Index(x) => write!(f, "{}", x),
        }
    }
}

pub fn modify(node: MNode, env: &mut Environment, modifier: fn(MNode, &mut Environment) -> MNode) -> MNode {
    match node {
        MNode::Prog(p) => {
            let mut prog = p.clone();
            prog.stmts = prog.stmts
                .iter()
                .map(|stmt| {
                    match modify(MNode::Stmt(stmt.clone()), env, modifier) {
                        MNode::Stmt(x) => x,
                        _ => stmt.clone(),
                    }
                })
                .collect::<Vec<Stmt>>();

            MNode::Prog(prog)
        },
        MNode::Stmt(s) => {
            match s {
                Stmt::Expression(ref e) => {
                    let mut expr_stmt = e.clone();
                    match modify(MNode::Expr(expr_stmt.expr), env, modifier) {
                        MNode::Expr(x) => {
                            expr_stmt.expr = x;
                            MNode::Stmt(Stmt::Expression(expr_stmt))
                        },
                        _ => MNode::Stmt(s.clone()),
                    }
                },
                Stmt::Block(b) => {
                    let mut block = b.clone();
                    block.stmts = block.stmts
                        .iter()
                        .map(|stmt| {
                            match modify(MNode::Stmt(stmt.clone()), env, modifier) {
                                MNode::Stmt(x) => x,
                                _ => stmt.clone(),
                            }
                        })
                    .collect::<Vec<Stmt>>();

                    MNode::Stmt(Stmt::Block(block))
                },
                Stmt::Return(r) => {
                    let mut ret = r.clone();
                    let retval = ret.retval;
                    ret.retval = match modify(MNode::Expr(retval.clone()), env,  modifier) {
                        MNode::Expr(x) => x,
                        _ => retval,
                    };

                    MNode::Stmt(Stmt::Return(ret))
                },
                Stmt::Let(l) => {
                    let mut let_stmt = l.clone();
                    let value = let_stmt.value;

                    let_stmt.value = match modify(MNode::Expr(value.clone()), env, modifier) {
                        MNode::Expr(x) => x,
                        _ => value,
                    };

                    MNode::Stmt(Stmt::Let(let_stmt))
                },
            }
        },
        MNode::Expr(ref e) => {
            match e {
                Expr::In(i) => {
                    let mut infix = i.clone();
                    let left = *infix.left;
                    infix.left = match modify(MNode::Expr(left.clone()), env, modifier) {
                        MNode::Expr(x) => Box::new(x),
                        _ => Box::new(left),
                    };

                    let right = *infix.right;
                    infix.right = match modify(MNode::Expr(right.clone()), env, modifier) {
                        MNode::Expr(x) => Box::new(x),
                        _ => Box::new(right),
                    };

                    MNode::Expr(Expr::In(infix))
                },
                Expr::Pre(p) => {
                    let mut prefix = p.clone();

                    let right = *prefix.right;
                    prefix.right = match modify(MNode::Expr(right.clone()), env, modifier) {
                        MNode::Expr(x) => Box::new(x),
                        _ => Box::new(right),
                    };

                    MNode::Expr(Expr::Pre(prefix))
                },
                Expr::Index(i) => {
                    let mut index_expr = i.clone();
                    let left = *index_expr.left;
                    index_expr.left = match modify(MNode::Expr(left.clone()), env, modifier) {
                        MNode::Expr(x) => Box::new(x),
                        _ => Box::new(left),
                    };

                    let index = *index_expr.index;
                    index_expr.index = match modify(MNode::Expr(index.clone()), env, modifier) {
                        MNode::Expr(x) => Box::new(x),
                        _ => Box::new(index),
                    };

                    MNode::Expr(Expr::Index(index_expr))
                },
                Expr::If(i) => {
                    let mut if_expr = i.clone();
                    let condition = *if_expr.condition;
                    if_expr.condition = match modify(MNode::Expr(condition.clone()), env, modifier) {
                        MNode::Expr(x) => Box::new(x),
                        _ => Box::new(condition),
                    };

                    let consequence = if_expr.consequence;
                    if_expr.consequence = match modify(MNode::Stmt(Stmt::Block(consequence.clone())), env, modifier) {
                        MNode::Stmt(x) => {
                            match x {
                                Stmt::Block(b) => b,
                                _ => consequence,
                            }
                        },
                        _ => consequence,
                    };

                    if let Some(alternative) = if_expr.alternative {
                        if_expr.alternative = match modify(MNode::Stmt(Stmt::Block(alternative.clone())), env, modifier) {
                            MNode::Stmt(x) => {
                                match x {
                                    Stmt::Block(b) => Some(b),
                                    _ => Some(alternative),
                                }
                            },
                            _ => Some(alternative),
                        };
                    }

                    MNode::Expr(Expr::If(if_expr))
                },
                Expr::Fn(f) => {
                    let mut func = f.clone();
                    func.params = func.params
                        .iter()
                        .map(|ident| {
                            match modify(MNode::Expr(Expr::Ident(ident.clone())), env, modifier) {
                                MNode::Expr(e) => {
                                    match e {
                                        Expr::Ident(i) => i,
                                        _ => ident.clone(),
                                    }
                                },
                                _ => ident.clone(),
                            }
                        })
                    .collect::<Vec<Identifier>>();

                    let block = func.body;
                    func.body = match modify(MNode::Stmt(Stmt::Block(block.clone())), env, modifier) {
                        MNode::Stmt(x) => {
                            match x {
                                Stmt::Block(b) => b,
                                _ => block,
                            }
                        },
                        _ => block,
                    };

                    MNode::Expr(Expr::Fn(func))
                },
                Expr::Array(a) => {
                    let mut array = a.clone();
                    array.elements = array.elements
                        .iter()
                        .map(|expr| {
                            match modify(MNode::Expr(expr.clone()), env, modifier) {
                                MNode::Expr(e) => e,
                                _ => expr.clone(),
                            }
                        })
                    .collect::<Vec<Expr>>();

                    MNode::Expr(Expr::Array(array))
                },
                Expr::Hash(h) => {
                    let mut hash = h.clone();
                    hash.pairs = hash.pairs
                        .iter()
                        .map(|(key, value)| {
                            let new_key = match modify(MNode::Expr(key.clone()), env, modifier) {
                                MNode::Expr(e) => e,
                                _ => key.clone(),
                            };

                            let new_value = match modify(MNode::Expr(value.clone()), env, modifier) {
                                MNode::Expr(v) => v,
                                _ => value.clone(),
                            };

                            (new_key, new_value)

                        })
                    .collect::<HashMap<Expr, Expr>>();

                    MNode::Expr(Expr::Hash(hash))
                },
                _ => modifier(node, env),
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lexer::token_type::TokenType,
        error::Result,
        interpreter::environment::Environment
    };

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

    #[test]
    fn test_modify() -> Result<()> {
        let one = || { Expr::Int(IntegerLiteral { token: Token { token_type: TokenType::INT, literal: "1".to_string() }, value: 1 }) };
        let two = || { Expr::Int(IntegerLiteral { token: Token { token_type: TokenType::INT, literal: "1".to_string() }, value: 2 }) };

        let tests = vec![
            (MNode::Expr(one()), MNode::Expr(two())),
            (
                MNode::Prog(
                    Program {
                        stmts: vec![
                            Stmt::Expression(
                                ExpressionStatement {
                                    token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                    expr: one(),
                                }
                            ),
                        ],
                    },
                ),
                MNode::Prog(
                    Program {
                        stmts: vec![
                            Stmt::Expression(
                                ExpressionStatement {
                                    token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                    expr: two(),
                                }
                            ),
                        ],
                    },
                ),
            ),
            (
                MNode::Expr(
                    Expr::In(
                        Infix {
                            token: Token { token_type: TokenType::PLUS, literal: "+".to_string() },
                            left: Box::new(one()),
                            operator: "+".to_string(),
                            right: Box::new(two()),
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::In(
                        Infix {
                            token: Token { token_type: TokenType::PLUS, literal: "+".to_string() },
                            left: Box::new(two()),
                            operator: "+".to_string(),
                            right: Box::new(two()),
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::In(
                        Infix {
                            token: Token { token_type: TokenType::PLUS, literal: "+".to_string() },
                            left: Box::new(two()),
                            operator: "+".to_string(),
                            right: Box::new(one()),
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::In(
                        Infix {
                            token: Token { token_type: TokenType::PLUS, literal: "+".to_string() },
                            left: Box::new(two()),
                            operator: "+".to_string(),
                            right: Box::new(two()),
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::Pre(
                        Prefix {
                            token: Token { token_type: TokenType::MINUS, literal: "-".to_string() },
                            operator: "-".to_string(),
                            right: Box::new(one()),
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::Pre(
                        Prefix {
                            token: Token { token_type: TokenType::MINUS, literal: "-".to_string() },
                            operator: "-".to_string(),
                            right: Box::new(two()),
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::Index(
                        IndexOperation {
                            token: Token { token_type: TokenType::LBRACKET, literal: "[".to_string() },
                            left: Box::new(one()),
                            index: Box::new(one()),
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::Index(
                        IndexOperation {
                            token: Token { token_type: TokenType::LBRACKET, literal: "[".to_string() },
                            left: Box::new(two()),
                            index: Box::new(two()),
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::If(
                        IfExpression {
                            token: Token { token_type: TokenType::IF, literal: "if".to_string() },
                            condition: Box::new(one()),
                            consequence: BlockStatement {
                                token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                                stmts: vec![
                                    Stmt::Expression(
                                        ExpressionStatement {
                                            token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                            expr: one(),
                                        },
                                    ),
                                ],
                            },
                            alternative: Some(
                                BlockStatement {
                                    token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                                    stmts: vec![
                                        Stmt::Expression(
                                            ExpressionStatement {
                                                token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                                expr: one(),
                                            },
                                        ),
                                    ],
                                },
                            ),
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::If(
                        IfExpression {
                            token: Token { token_type: TokenType::IF, literal: "if".to_string() },
                            condition: Box::new(two()),
                            consequence: BlockStatement {
                                token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                                stmts: vec![
                                    Stmt::Expression(
                                        ExpressionStatement {
                                            token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                            expr: two(),
                                        },
                                    ),
                                ],
                            },
                            alternative: Some(
                                BlockStatement {
                                    token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                                    stmts: vec![
                                        Stmt::Expression(
                                            ExpressionStatement {
                                                token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                                expr: two(),
                                            },
                                        ),
                                    ],
                                },
                            ),
                        },
                    ),
                ),
            ),
            (
                MNode::Stmt(
                    Stmt::Return(
                        ReturnStatement {
                            token: Token { token_type: TokenType::RBRACKET, literal: "return".to_string() },
                            retval: one(),
                        },
                    ),
                ),
                MNode::Stmt(
                    Stmt::Return(
                        ReturnStatement {
                            token: Token { token_type: TokenType::RBRACKET, literal: "return".to_string() },
                            retval: two(),
                        },
                    ),
                ),
            ),
            (
                MNode::Stmt(
                    Stmt::Let(
                        LetStatement {
                            token: Token { token_type: TokenType::LET, literal: "let".to_string() },
                            name: Identifier {
                                token: Token { token_type: TokenType::IDENT, literal: "a".to_string() },
                                value: "a".to_string()
                            },
                            value: one(),
                        },
                    ),
                ),
                MNode::Stmt(
                    Stmt::Let(
                        LetStatement {
                            token: Token { token_type: TokenType::LET, literal: "let".to_string() },
                            name: Identifier {
                                token: Token { token_type: TokenType::IDENT, literal: "a".to_string() },
                                value: "a".to_string()
                            },
                            value: two(),
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::Fn(
                        FnLiteral {
                            token: Token { token_type: TokenType::LET, literal: "let".to_string() },
                            name: None,
                            params: vec![],
                            body: BlockStatement {
                                token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                                stmts: vec![
                                    Stmt::Expression(
                                        ExpressionStatement {
                                            token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                            expr: one(),
                                        },
                                    ),
                                ],
                            },
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::Fn(
                        FnLiteral {
                            token: Token { token_type: TokenType::LET, literal: "let".to_string() },
                            name: None,
                            params: vec![],
                            body: BlockStatement {
                                token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                                stmts: vec![
                                    Stmt::Expression(
                                        ExpressionStatement {
                                            token: Token { token_type: TokenType::INT, literal: "1".to_string() },
                                            expr: two(),
                                        },
                                    ),
                                ],
                            },
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::Array(
                        ArrayLiteral {
                            token: Token { token_type: TokenType::LBRACKET, literal: "[".to_string() },
                            elements: vec![one()],
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::Array(
                        ArrayLiteral {
                            token: Token { token_type: TokenType::LBRACKET, literal: "[".to_string() },
                            elements: vec![two()],
                        },
                    ),
                ),
            ),
            (
                MNode::Expr(
                    Expr::Hash(
                        HashLiteral {
                            token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                            pairs: HashMap::from([
                                (one(), one()),
                            ]),
                        },
                    ),
                ),
                MNode::Expr(
                    Expr::Hash(
                        HashLiteral {
                            token: Token { token_type: TokenType::LBRACE, literal: "{".to_string() },
                            pairs: HashMap::from([
                                (two(), two()),
                            ]),
                        },
                    ),
                ),
            ),
        ];

        let turn_one_into_two = |node: MNode, _: &mut Environment| -> MNode {
            if let MNode::Expr(ref e) = node {
                if let Expr::Int(i) = e {
                    if i.value == 1 {
                        let mut lit = i.clone();
                        lit.value = 2;
                        return MNode::Expr(Expr::Int(lit));
                    };
                }
            }
            node
        };

        let env = &mut Environment::new();

        for tt in tests {
            let modified = modify(tt.0, env, turn_one_into_two);
            assert_eq!(tt.1, modified);
        };

        Ok(())
    }
}

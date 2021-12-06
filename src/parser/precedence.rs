use std::collections::HashMap;

use crate::lexer::token_type::TokenType;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum Precedence {
    LOWEST,
    EQUALS,      // ==
    LESSGREATER, // > or <
    SUM,         // +
    PRODUCT,     // *
    PREFIX,      // -X or !X
    CALL,        // myFunction(X)
}

pub fn compute_priority_map(map: &mut HashMap<TokenType, Precedence>) {
    let precedences = [
        (TokenType::EQ,       Precedence::EQUALS),
        (TokenType::NOT_EQ,   Precedence::EQUALS),
        (TokenType::LT,       Precedence::LESSGREATER),
        (TokenType::GT,       Precedence::LESSGREATER),
        (TokenType::PLUS,     Precedence::SUM),
        (TokenType::MINUS,    Precedence::SUM),
        (TokenType::SLASH,    Precedence::PRODUCT),
        (TokenType::ASTERISK, Precedence::PRODUCT),
    ];

    for t in precedences {
        map.insert(t.0, t.1);
    };
}

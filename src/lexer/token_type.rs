use std::collections::HashMap;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum TokenType {
    ILLEGAL,
    EOF,

    // Identifiers + literals
    IDENT,
    INT,

    // Operators
    ASSIGN,
    PLUS,

    // Delimiters
    COMMA,
    SEMICOLON,

    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,

    // Keywords
    FUNCTION,
    LET,
}

pub fn compute_keyword_map(map: &mut HashMap<&'static str, TokenType>) {
    let keywords = [
        ("fn", TokenType::FUNCTION),
        ("let", TokenType::LET),
    ];

    for t in keywords {
        map.insert(t.0, t.1);
    };
}

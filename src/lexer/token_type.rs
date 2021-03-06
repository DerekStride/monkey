use std::collections::HashMap;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum TokenType {
    ILLEGAL,
    EOF,

    // Identifiers + literals
    STRING,
    IDENT,
    INT,

    // Operators
    ASSIGN,
    PLUS,
    MINUS,
    BANG,
    ASTERISK,
    SLASH,

    LT,
    GT,

    EQ,
    #[allow(non_camel_case_types)]
    NOT_EQ,

    // Delimiters
    COMMA,
    SEMICOLON,
    COLON,

    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,
    LBRACKET,
    RBRACKET,

    // Keywords
    FUNCTION,
    LET,
    TRUE,
    FALSE,
    IF,
    ELSE,
    RETURN,
    MACRO,
}

pub fn compute_keyword_map(map: &mut HashMap<&'static str, TokenType>) {
    let keywords = [
        ("fn", TokenType::FUNCTION),
        ("let", TokenType::LET),
        ("true", TokenType::TRUE),
        ("false", TokenType::FALSE),
        ("if", TokenType::IF),
        ("else", TokenType::ELSE),
        ("return", TokenType::RETURN),
        ("macro", TokenType::MACRO),
    ];

    for t in keywords {
        map.insert(t.0, t.1);
    };
}

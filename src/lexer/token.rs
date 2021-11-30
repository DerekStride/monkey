use crate::lexer::token_type::TokenType;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Token {
    pub token_type: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_type: TokenType, literal: String) -> Self {
        Self { token_type, literal }
    }
}

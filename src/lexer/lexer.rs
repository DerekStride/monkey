use std::{io, str};
use std::iter::Peekable;
use std::collections::HashMap;

use crate::error::Error;
use crate::lexer::token::Token;
use crate::lexer::token_type::TokenType;

type Result<T> = std::result::Result<T, Error>;
type FileByte = std::result::Result<u8, io::Error>;

pub struct Lexer<I: Iterator<Item = FileByte>> {
    input: Peekable<I>,
    ch: u8,
    keyword_map: HashMap<&'static str, TokenType>,
}

impl<I: Iterator<Item = FileByte>> Iterator for Lexer<I> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            Ok(Token { token_type: TokenType::EOF, .. }) => None,
            Ok(tok) => Some(Ok(tok)),
            Err(e) =>  Some(Err(e)),
        }
    }
}

impl<I: Iterator<Item = FileByte>> Lexer<I> {
    pub fn new(mut input: Peekable<I>) -> Result<Self> {
        let ch = match input.next() {
            Some(ch) => ch?,
            None => 0,
        };

        let lex = Self {
            input,
            ch,
            keyword_map: HashMap::new()
        };

        Ok(lex)
    }

    pub fn next_token(&mut self) -> Result<Token> {
        self.eat_whitespace()?;
        let ch = self.ch;

        let tok = match ch {
            b'=' => {
                let peeked = self.peek_char()?;
                if peeked == b'=' {
                    self.next_char()?;
                    new_token(TokenType::EQ, &[ch, peeked])?
                } else {
                    new_token(TokenType::ASSIGN, &[ch])?
                }
            },
            b';' => new_token(TokenType::SEMICOLON, &[ch])?,
            b'(' => new_token(TokenType::LPAREN, &[ch])?,
            b')' => new_token(TokenType::RPAREN, &[ch])?,
            b',' => new_token(TokenType::COMMA, &[ch])?,
            b'+' => new_token(TokenType::PLUS, &[ch])?,
            b'-' => new_token(TokenType::MINUS, &[ch])?,
            b'*' => new_token(TokenType::ASTERISK, &[ch])?,
            b'/' => new_token(TokenType::SLASH, &[ch])?,
            b'<' => new_token(TokenType::LT, &[ch])?,
            b'>' => new_token(TokenType::GT, &[ch])?,
            b'!' => {
                let peeked = self.peek_char()?;
                if peeked == b'=' {
                    self.next_char()?;
                    new_token(TokenType::NOT_EQ, &[ch, peeked])?
                } else {
                    new_token(TokenType::BANG, &[ch])?
                }
            },
            b'{' => new_token(TokenType::LBRACE, &[ch])?,
            b'}' => new_token(TokenType::RBRACE, &[ch])?,
            b'"' => {
                let string_lit = self.read_string()?;
                Token::new(TokenType::STRING, string_lit)
            },
            0 => new_token(TokenType::EOF, &[])?,
            _ => {
                if is_letter(ch) {
                    let ident = self.read_identifier()?;
                    let tok_type = self.lookup_ident(&ident);

                    Token::new(tok_type, ident)
                } else if is_digit(ch) {
                    let num = self.read_number()?;

                    Token::new(TokenType::INT, num)
                } else {
                    new_token(TokenType::ILLEGAL, &[])?
                }
            },
        };

        self.next_char()?;

        Ok(tok)
    }

    fn eat_whitespace(&mut self) -> Result<()> {
        let mut ch = self.ch;

        while ch == b' ' || ch == b'\t' || ch == b'\n' || ch == b'\r' {
            ch = self.next_char()?;
        }

        Ok(())
    }

    fn next_char(&mut self) -> Result<u8> {
        self.ch = match self.input.next() {
            Some(ch) => ch?,
            None => 0,
        };
        Ok(self.ch)
    }

    fn peek_char(&mut self) -> Result<u8> {
        match self.input.peek() {
            Some(peeked) => {
                match peeked.as_ref() {
                    Ok(c) => Ok(*c),
                    Err(e) => Err(Error::new(format!("{}", e))),
                }
            },
            None => Ok(0),
        }
    }

    fn read_identifier(&mut self) -> Result<String> {
        let mut ident = Vec::new();
        let mut ch = self.peek_char()?;
        ident.push(self.ch);

        while is_letter(ch) {
            self.next_char()?;
            ident.push(ch);
            ch = self.peek_char()?;
        }

        Ok(String::from_utf8(ident)?)
    }

    fn read_number(&mut self) -> Result<String> {
        let ident = &mut Vec::<u8>::new();
        let mut ch = self.peek_char()?;
        ident.push(self.ch);

        while is_digit(ch) {
            self.next_char()?;
            ident.push(ch);
            ch = self.peek_char()?;
        }

        Ok(String::from_utf8(ident.to_vec())?)
    }

    fn read_string(&mut self) -> Result<String> {
        self.next_char()?;
        let mut string_lit = Vec::new();

        while self.ch != b'"' {
            string_lit.push(self.ch);
            self.next_char()?;
        }

        Ok(String::from_utf8(string_lit)?)
    }

    fn lookup_ident(&mut self, ident: &str) -> TokenType {
        if self.keyword_map.is_empty() {
            super::token_type::compute_keyword_map(&mut self.keyword_map);
        }

        match self.keyword_map.get(ident) {
            Some(&tok) => tok,
            None => TokenType::IDENT,
        }
    }
}

#[inline]
fn new_token(t: TokenType, literal: &[u8]) -> Result<Token> {
    Ok(Token::new(t, str::from_utf8(literal)?.to_string()))
}

#[inline]
fn is_letter(ch: u8) -> bool {
    b'a' <= ch && ch <= b'z' ||
        b'A' <= ch && ch <= b'Z' ||
        ch == b'_'
}

#[inline]
fn is_digit(ch: u8) -> bool {
    b'0' <= ch && ch <= b'9'
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;

    struct Expected {
        expected_type: TokenType,
        expected_literal: String,
    }

    fn lex<I: Iterator<Item = FileByte>>(input: I) -> Lexer<I> {
        Lexer::new(input.peekable()).unwrap()
    }

    fn assert_tokens<I: Iterator<Item = FileByte>>(expected: Vec<Expected>, lex: &mut Lexer<I>) {
        for t in expected {
            let tok = lex.next_token().unwrap();
            assert_eq!(t.expected_type, tok.token_type);
            assert_eq!(t.expected_literal, tok.literal);
        }
    }

    #[test]
    fn test_next_token() {
        let input = b"=+(){},;".to_vec();
        let l = &mut lex(input.bytes());

        let tests = vec![
            Expected { expected_type: TokenType::ASSIGN, expected_literal: "=".to_string() },
            Expected { expected_type: TokenType::PLUS, expected_literal: "+".to_string() },
            Expected { expected_type: TokenType::LPAREN, expected_literal: "(".to_string() },
            Expected { expected_type: TokenType::RPAREN, expected_literal: ")".to_string() },
            Expected { expected_type: TokenType::LBRACE, expected_literal: "{".to_string() },
            Expected { expected_type: TokenType::RBRACE, expected_literal: "}".to_string() },
            Expected { expected_type: TokenType::COMMA, expected_literal: ",".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::EOF, expected_literal: "".to_string() },
        ];

        assert_tokens(tests, l);
    }

    #[test]
    fn test_monkey_program() {
        let input = br###"
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
                x + y;
            };

            let result = add(five, ten);
        "###.to_vec();
        let l = &mut lex(input.bytes());

        let tests = vec![
            Expected { expected_type: TokenType::LET, expected_literal: "let".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "five".to_string() },
            Expected { expected_type: TokenType::ASSIGN, expected_literal: "=".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "5".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::LET, expected_literal: "let".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "ten".to_string() },
            Expected { expected_type: TokenType::ASSIGN, expected_literal: "=".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "10".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::LET, expected_literal: "let".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "add".to_string() },
            Expected { expected_type: TokenType::ASSIGN, expected_literal: "=".to_string() },
            Expected { expected_type: TokenType::FUNCTION, expected_literal: "fn".to_string() },
            Expected { expected_type: TokenType::LPAREN, expected_literal: "(".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "x".to_string() },
            Expected { expected_type: TokenType::COMMA, expected_literal: ",".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "y".to_string() },
            Expected { expected_type: TokenType::RPAREN, expected_literal: ")".to_string() },
            Expected { expected_type: TokenType::LBRACE, expected_literal: "{".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "x".to_string() },
            Expected { expected_type: TokenType::PLUS, expected_literal: "+".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "y".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::RBRACE, expected_literal: "}".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::LET, expected_literal: "let".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "result".to_string() },
            Expected { expected_type: TokenType::ASSIGN, expected_literal: "=".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "add".to_string() },
            Expected { expected_type: TokenType::LPAREN, expected_literal: "(".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "five".to_string() },
            Expected { expected_type: TokenType::COMMA, expected_literal: ",".to_string() },
            Expected { expected_type: TokenType::IDENT, expected_literal: "ten".to_string() },
            Expected { expected_type: TokenType::RPAREN, expected_literal: ")".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::EOF, expected_literal: "".to_string() },
        ];

        assert_tokens(tests, l);
    }

    #[test]
    fn test_monkey_symbols() {
        let input = br###"
            !-/*5;
            5 < 10 > 5;

            if (5 < 10) {
                return true;
            } else {
                return false;
            }

            10 == 10;
            10 != 9;
            "foobar"
            "foo bar"
        "###.to_vec();
        let l = &mut lex(input.bytes());

        let tests = vec![
            Expected { expected_type: TokenType::BANG, expected_literal: "!".to_string() },
            Expected { expected_type: TokenType::MINUS, expected_literal: "-".to_string() },
            Expected { expected_type: TokenType::SLASH, expected_literal: "/".to_string() },
            Expected { expected_type: TokenType::ASTERISK, expected_literal: "*".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "5".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "5".to_string() },
            Expected { expected_type: TokenType::LT, expected_literal: "<".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "10".to_string() },
            Expected { expected_type: TokenType::GT, expected_literal: ">".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "5".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::IF, expected_literal: "if".to_string() },
            Expected { expected_type: TokenType::LPAREN, expected_literal: "(".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "5".to_string() },
            Expected { expected_type: TokenType::LT, expected_literal: "<".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "10".to_string() },
            Expected { expected_type: TokenType::RPAREN, expected_literal: ")".to_string() },
            Expected { expected_type: TokenType::LBRACE, expected_literal: "{".to_string() },
            Expected { expected_type: TokenType::RETURN, expected_literal: "return".to_string() },
            Expected { expected_type: TokenType::TRUE, expected_literal: "true".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::RBRACE, expected_literal: "}".to_string() },
            Expected { expected_type: TokenType::ELSE, expected_literal: "else".to_string() },
            Expected { expected_type: TokenType::LBRACE, expected_literal: "{".to_string() },
            Expected { expected_type: TokenType::RETURN, expected_literal: "return".to_string() },
            Expected { expected_type: TokenType::FALSE, expected_literal: "false".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::RBRACE, expected_literal: "}".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "10".to_string() },
            Expected { expected_type: TokenType::EQ, expected_literal: "==".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "10".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "10".to_string() },
            Expected { expected_type: TokenType::NOT_EQ, expected_literal: "!=".to_string() },
            Expected { expected_type: TokenType::INT, expected_literal: "9".to_string() },
            Expected { expected_type: TokenType::SEMICOLON, expected_literal: ";".to_string() },
            Expected { expected_type: TokenType::STRING, expected_literal: "foobar".to_string() },
            Expected { expected_type: TokenType::STRING, expected_literal: "foo bar".to_string() },
            Expected { expected_type: TokenType::EOF, expected_literal: "".to_string() },
        ];

        assert_tokens(tests, l);
    }
}

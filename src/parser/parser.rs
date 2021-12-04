use std::iter::Peekable;

use crate::{
    lexer::{
        token::Token,
        token_type::TokenType,
    },
    error::Error,
    ast::*,
};

type Result<T> = std::result::Result<T, Error>;

struct Parser<I: Iterator<Item = Result<Token>>> {
    l: Peekable<I>,
    tok: Token,
    errors: Vec<String>,
}

impl<I: Iterator<Item = Result<Token>>> Parser<I> {
    pub fn new(mut l: Peekable<I>) -> Result<Self> {
        let tok = match l.next() {
            Some(t) => t?,
            None => return Err(Error::new(String::from("Unexpected EOF."))),
        };

        let p = Self {
            l,
            tok,
            errors: Vec::new(),
        };

        Ok(p)
    }

    pub fn parse(&mut self) -> Result<Program> {
        let mut program = Program::new();

        while !self.curr_token_is(TokenType::EOF) {
            if let Some(stmt) = self.parse_statement() {
                program.stmts.push(stmt);
            }
            self.next_token()?;
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> Option<Stmt> {
        match self.tok.token_type {
            TokenType::LET => self.parse_let_statement(),
            TokenType::RETURN => self.parse_return_statement(),
            _ => None,
        }
    }

    fn parse_let_statement(&mut self) -> Option<Stmt> {
        let token = self.tok.clone();

        self.expect_peek(TokenType::IDENT)?;

        let name = Identifier {
            token: self.tok.clone(),
            value: self.tok.literal.clone(),
        };

        self.expect_peek(TokenType::ASSIGN)?;

        while !self.curr_token_is(TokenType::SEMICOLON) {
            if let Err(_) = self.next_token() {
                return None;
            };
        }

        Some(
            Stmt::Let(
                LetStatement {
                    token,
                    name: name.clone(), // todo: remove clone when not using in value
                    value: Expr::Ident(name.clone()),
                }
            )
        )
    }

    fn parse_return_statement(&mut self) -> Option<Stmt> {
        let token = self.tok.clone();

        if let Err(_) = self.next_token() {
            return None;
        }

        while !self.curr_token_is(TokenType::SEMICOLON) {
            if let Err(_) = self.next_token() {
                return None;
            };
        }

        Some(
            Stmt::Return(
                ReturnStatement {
                    token,
                    retval: Expr::Ident(Identifier { token: self.tok.clone(), value: "todo".to_string() } ),
                }
            )
        )
    }

    fn next_token(&mut self) -> Result<()> {
        self.tok = match self.l.next() {
            Some(t) => t?,
            None => Token { token_type: TokenType::EOF, literal: String::from("") },
        };
        Ok(())
    }

    fn expect_peek(&mut self, t: TokenType) -> Option<()> {
        if self.peek_token_is(t) {
            match self.next_token() {
                Ok(_) => Some(()),
                Err(_) => None,
            }
        } else {
            self.peek_error(t);
            None
        }
    }

    fn curr_token_is(&self, t: TokenType) -> bool {
        self.tok.token_type == t
    }

    fn peek_token_is(&mut self, t: TokenType) -> bool {
        if let Some(peeked) = self.l.peek() {
            match peeked {
                Ok(tok) => tok.token_type == t,
                Err(_) => false,
            }
        } else {
            t == TokenType::EOF
        }
    }

    fn peek_error(&mut self, t: TokenType) {
        let actual = if let Some(peeked) = self.l.peek() {
            match peeked {
                Ok(tok) => tok.token_type,
                Err(_) => TokenType::ILLEGAL,
            }
        } else {
            TokenType::EOF
        };
        let msg = format!("Expected next token to be {:?}, got {:?} instead.", t, actual);
        self.errors.push(msg);
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::Node, lexer::lexer::Lexer};

    use super::*;
    use std::io::{self, Read};

    type FileByte = std::result::Result<u8, io::Error>;

    struct Expected {
        expected_ident: String,
    }

    fn parse<I: Iterator<Item = FileByte>>(input: I) -> Result<Program> {
        let l = Lexer::new(input.peekable())?;
        let mut p = Parser::new(l.peekable())?;
        let program = p.parse()?;

        check_parser_errors(p)?;

        Ok(program)
    }

    fn test_let_statement(stmt: &Stmt, expected_ident: &String) {
        assert_eq!("let", stmt.token_literal());

        let let_stmt = match stmt {
            Stmt::Let(l) => l,
            _ => panic!("Expected let statement. Got {:?}", stmt),
        };

        assert_eq!(*expected_ident, let_stmt.name.value);
    }

    fn check_parser_errors<I: Iterator<Item = Result<Token>>>(p: Parser<I>) -> Result<()> {
        if p.errors.is_empty() {
            return Ok(());
        }

        let mut msg = format!("The Parser had {} errors:\n", p.errors.len());

        for e in p.errors {
            msg.push_str(&e);
            msg.push('\n');
        }

        Err(Error::new(msg))
    }


    #[test]
    fn test_let_statements() -> Result<()> {
        let input = br###"
            let x = 5;
            let y = 10;
            let foobar = 838383;
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(3, program.stmts.len());

        let tests = vec![
            Expected { expected_ident: "x".to_string() },
            Expected { expected_ident: "y".to_string() },
            Expected { expected_ident: "foobar".to_string() },
        ];

        for (i, t) in tests.iter().enumerate() {
            if let Some(stmt) = program.stmts.get(i) {
                test_let_statement(stmt, &t.expected_ident);
            } else {
                panic!("Statement {} was missing", i);
            }
        }

        Ok(())
    }

    #[test]
    fn test_parser_errors() -> Result<()> {
        let input = br###"
            let x 5;
            let = 10;
            let 838383;
        "###.to_vec();

        let l = Lexer::new(input.bytes().peekable())?;
        let mut p = Parser::new(l.peekable())?;
        p.parse()?;

        assert_eq!(3, p.errors.len());

        let tests = vec![
            (TokenType::ASSIGN, TokenType::INT),
            (TokenType::IDENT, TokenType::ASSIGN),
            (TokenType::IDENT, TokenType::INT),
        ];

        for (i, err) in p.errors.iter().enumerate() {
            let test = tests.get(i).unwrap();

            let msg = format!("Expected next token to be {:?}, got {:?} instead.", test.0, test.1);
            assert_eq!(msg, *err);
        }

        Ok(())
    }

    #[test]
    fn test_return_statement() -> Result<()> {
        let input = br###"
            return 5;
            return 10;
            return 993322;
        "###.to_vec();

        let program = parse(input.bytes())?;

        assert_eq!(3, program.stmts.len());

        for stmt in program.stmts {
            assert_eq!("return", stmt.token_literal());

            if let Stmt::Return(_) = stmt {
                continue
            } else {
                panic!("Statement {:?} was not a Stmt::Return.", stmt);
            }
        }

        Ok(())
    }
}

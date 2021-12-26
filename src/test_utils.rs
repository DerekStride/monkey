use std::io::Read;

use crate::{
    ast::*,
    interpreter::object::*,
    error::{Result, Error},
    lexer::{
        lexer::Lexer,
        token::Token,
        token_type::TokenType,
    },
    parser::parser::Parser,
};

pub fn i_to_o(i: i128) -> MObject {
    MObject::Int(
        Integer {
            value: i,
        }
    )
}

pub fn i_to_expr(i: i128) -> Expr {
    Expr::Int(
        IntegerLiteral {
            token: Token { literal: format!("{}", i), token_type: TokenType::INT },
            value: i,
        }
        )
}

pub fn b_to_expr(i: bool) -> Expr {
    Expr::Bool(
        BooleanLiteral {
            token: Token { literal: format!("{}", i), token_type: if i { TokenType::TRUE } else { TokenType::FALSE } },
            value: i,
        }
        )
}

pub fn l_to_expr(i: String) -> Expr {
    Expr::Ident(
        Identifier {
            token: Token { literal: i.clone(), token_type: TokenType::IDENT },
            value: i,
        }
        )
}

pub fn s_to_expr(i: String) -> Expr {
    Expr::Str(
        StringLiteral {
            token: Token { literal: i.clone(), token_type: TokenType::STRING },
            value: i,
        }
        )
}

pub fn parse(input: String) -> Result<Program> {
    let lexer = Lexer::new(input.as_bytes().bytes().peekable())?;
    let mut parser = Parser::new(lexer.peekable())?;
    let program = parser.parse()?;

    check_parser_errors(parser)?;

    Ok(program)
}


pub fn check_parser_errors<I: Iterator<Item = Result<Token>>>(p: Parser<I>) -> Result<()> {
    let errors = p.errors();

    if errors.is_empty() { return Ok(()); };

    let mut msg = format!("The Parser had {} errors:\n", errors.len());

    for e in errors {
        msg.push_str(&e);
        msg.push('\n');
    }

    Err(Error::new(msg))
}

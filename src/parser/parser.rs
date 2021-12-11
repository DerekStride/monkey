use std::{iter::Peekable, collections::HashMap};

use crate::{
    lexer::{
        token::Token,
        token_type::TokenType,
    },
    parser::precedence::Precedence,
    error::Error,
    ast::*,
};

type Result<T> = std::result::Result<T, Error>;

pub struct Parser<I: Iterator<Item = Result<Token>>> {
    l: Peekable<I>,
    tok: Token,
    errors: Vec<String>,
    prefix_parse_fns: HashMap<TokenType, fn(&mut Self) -> Option<Expr>>,
    infix_parse_fns: HashMap<TokenType, fn(&mut Self, Expr) -> Option<Expr>>,
    precedences: HashMap<TokenType, Precedence>,
}

impl<I: Iterator<Item = Result<Token>>> Parser<I> {
    pub fn new(mut l: Peekable<I>) -> Result<Self> {
        let tok = match l.next() {
            Some(t) => t?,
            None => return Err(Error::new(String::from("Unexpected EOF."))),
        };

        let mut precedences = HashMap::new();
        super::precedence::compute_priority_map(&mut precedences);

        let mut p = Self {
            l,
            tok,
            errors: Vec::new(),
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
            precedences,
        };

        p.register_prefix(TokenType::IDENT, Self::parse_identifier);
        p.register_prefix(TokenType::INT, Self::parse_integer_literal);
        p.register_prefix(TokenType::TRUE, Self::parse_boolean);
        p.register_prefix(TokenType::FALSE, Self::parse_boolean);
        p.register_prefix(TokenType::BANG, Self::parse_prefix_expression);
        p.register_prefix(TokenType::MINUS, Self::parse_prefix_expression);
        p.register_prefix(TokenType::LPAREN, Self::parse_grouped_expression);
        p.register_prefix(TokenType::IF, Self::parse_if_expression);
        p.register_prefix(TokenType::FUNCTION, Self::parse_function_expression);

        p.register_infix(TokenType::PLUS, Self::parse_infix_expression);
        p.register_infix(TokenType::MINUS, Self::parse_infix_expression);
        p.register_infix(TokenType::SLASH, Self::parse_infix_expression);
        p.register_infix(TokenType::ASTERISK, Self::parse_infix_expression);
        p.register_infix(TokenType::EQ, Self::parse_infix_expression);
        p.register_infix(TokenType::NOT_EQ, Self::parse_infix_expression);
        p.register_infix(TokenType::LT, Self::parse_infix_expression);
        p.register_infix(TokenType::GT, Self::parse_infix_expression);
        p.register_infix(TokenType::LPAREN, Self::parse_call_expression);

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

    pub fn errors(&self) -> Vec<String> {
        self.errors.clone()
    }

    fn parse_statement(&mut self) -> Option<Stmt> {
        match self.tok.token_type {
            TokenType::LET => self.parse_let_statement(),
            TokenType::RETURN => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
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

        self.ignore_next()?;

        let value = self.parse_expression(Precedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.ignore_next()?;
        }

        Some(
            Stmt::Let(
                LetStatement {
                    token,
                    name,
                    value,
                }
            )
        )
    }

    fn parse_return_statement(&mut self) -> Option<Stmt> {
        let token = self.tok.clone();

        self.ignore_next()?;

        let retval = self.parse_expression(Precedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.ignore_next()?;
        }

        Some(
            Stmt::Return(
                ReturnStatement {
                    token,
                    retval,
                }
            )
        )
    }

    fn parse_block_statement(&mut self) -> Option<BlockStatement> {
        let token = self.tok.clone();
        let mut stmts = Vec::new();

        self.ignore_next()?;

        while !self.curr_token_is(TokenType::RBRACE) && !self.curr_token_is(TokenType::EOF) {
            if let Some(stmt) = self.parse_statement() {
                stmts.push(stmt);
            }
            self.ignore_next()?;
        }

        Some(
            BlockStatement {
                token,
                stmts,
            }
        )
    }

    fn parse_expression_statement(&mut self) -> Option<Stmt> {
        let token = self.tok.clone();
        let expr = self.parse_expression(Precedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.ignore_next()?;
        }

        Some(
            Stmt::Expression(
                ExpressionStatement {
                    token,
                    expr,
                }
            )
        )
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Option<Expr> {
        let mut left = if let Some(prefix) = self.prefix_parse_fns.get(&self.tok.token_type) {
            prefix(self)?
        } else {
            self.errors.push(format!("Prefix parse function for {:?} not found.", self.tok.token_type));
            return None;
        };

        while !self.peek_token_is(TokenType::SEMICOLON) && precedence < self.peek_precedence() {
            let peeked = match self.l.peek() {
                Some(p) => match p {
                    Ok(tok) => tok.clone(),
                    Err(_) => return Some(left),
                },
                None => return Some(left),
            };
            if let Err(_) = self.next_token() { return Some(left) };

            left = if let Some(infix) = self.infix_parse_fns.get(&peeked.token_type) {
                infix(self, left)?
            } else {
                return Some(left);
            };
        }

        Some(left)
    }

    fn parse_identifier(&mut self) -> Option<Expr> {
        Some(
            Expr::Ident(
                Identifier {
                    token: self.tok.clone(),
                    value: self.tok.literal.clone(),
                }
            )
        )
    }

    fn parse_integer_literal(&mut self) -> Option<Expr> {
        let lit = match self.tok.literal.parse::<i128>() {
            Ok(x) => x,
            Err(_) => {
                self.errors.push(format!("Could not parse {} as integer", self.tok.literal));
                return None
            },
        };

        Some(
            Expr::Int(
                IntegerLiteral {
                    token: self.tok.clone(),
                    value: lit,
                }
            )
        )
    }

    fn parse_boolean(&mut self) -> Option<Expr> {
        Some(
            Expr::Bool(
                BooleanLiteral {
                    token: self.tok.clone(),
                    value: self.curr_token_is(TokenType::TRUE),
                }
            )
        )
    }

    fn parse_grouped_expression(&mut self) -> Option<Expr> {
        self.ignore_next()?;

        let exp = self.parse_expression(Precedence::LOWEST);

        self.expect_peek(TokenType::RPAREN)?;

        exp
    }

    fn parse_if_expression(&mut self) -> Option<Expr> {
        let token = self.tok.clone();

        self.expect_peek(TokenType::LPAREN)?;
        self.ignore_next()?;

        let condition = self.parse_expression(Precedence::LOWEST)?;

        self.expect_peek(TokenType::RPAREN)?;
        self.expect_peek(TokenType::LBRACE)?;

        let consequence = self.parse_block_statement()?;
        let mut alternative: Option<BlockStatement> = None;

        if self.peek_token_is(TokenType::ELSE) {
            self.ignore_next()?;
            self.expect_peek(TokenType::LBRACE)?;

            alternative = self.parse_block_statement();
        }

        Some(
            Expr::If(
                IfExpression {
                    token,
                    condition: Box::new(condition),
                    consequence,
                    alternative,
                }
            )
        )
    }

    fn parse_function_parameters(&mut self) -> Vec<Identifier> {
        let mut params = Vec::new();

        if self.peek_token_is(TokenType::RPAREN) {
            if let Err(_) = self.next_token() { return params; };
            return params;
        };
        if let Err(_) = self.next_token() { return params; };

        params.push(Identifier { token: self.tok.clone(), value: self.tok.literal.clone() });

        while self.peek_token_is(TokenType::COMMA) {
            if let Err(_) = self.next_token() { return params; };
            if let Err(_) = self.next_token() { return params; };
            params.push(Identifier { token: self.tok.clone(), value: self.tok.literal.clone() });
        }

        match self.expect_peek(TokenType::RPAREN) {
            Some(_) => params,
            None => params,
        }
    }

    fn parse_function_expression(&mut self) -> Option<Expr> {
        let token = self.tok.clone();

        self.expect_peek(TokenType::LPAREN)?;

        let params = self.parse_function_parameters();

        self.expect_peek(TokenType::LBRACE)?;

        let body = self.parse_block_statement()?;

        Some(
            Expr::Fn(
                FnLiteral {
                    token,
                    params,
                    body,
                }
            )
        )
    }

    fn parse_prefix_expression(&mut self) -> Option<Expr> {
        let token = self.tok.clone();
        let operator = token.literal.clone();

        self.ignore_next()?;

        let right = self.parse_expression(Precedence::PREFIX)?;

        Some(
            Expr::Pre(
                Prefix {
                    token,
                    operator,
                    right: Box::new(right),
                }
            )
        )
    }

    fn parse_infix_expression(&mut self, left: Expr) -> Option<Expr> {
        let token = self.tok.clone();
        let operator = token.literal.clone();
        let precedence = self.curr_precedence();

        self.ignore_next()?;

        let right = self.parse_expression(precedence)?;

        Some(
            Expr::In(
                Infix {
                    token,
                    left: Box::new(left),
                    operator,
                    right: Box::new(right),
                }
            )
        )
    }

    fn parse_call_arguments(&mut self) -> Vec<Expr> {
        let mut args = Vec::new();

        if self.peek_token_is(TokenType::RPAREN) {
            if let Err(_) = self.next_token() { return args; };
            return args;
        };
        if let Err(_) = self.next_token() { return args; };

        if let Some(expr) = self.parse_expression(Precedence::LOWEST) {
            args.push(expr);
        } else {
            return args;
        }

        while self.peek_token_is(TokenType::COMMA) {
            if let Err(_) = self.next_token() { return args; };
            if let Err(_) = self.next_token() { return args; };

            if let Some(expr) = self.parse_expression(Precedence::LOWEST) {
                args.push(expr);
            } else {
                return args;
            }
        }

        match self.expect_peek(TokenType::RPAREN) {
            Some(_) => args,
            None => args,
        }
    }

    fn parse_call_expression(&mut self, function: Expr) -> Option<Expr> {
        let token = self.tok.clone();
        let args = self.parse_call_arguments();

        Some(
            Expr::Call(
                FnCall {
                    token,
                    function: Box::new(function),
                    args,
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

    fn ignore_next(&mut self) -> Option<()> {
        match self.next_token() {
            Ok(_) => Some(()),
            Err(_) => None,
        }
    }

    fn expect_peek(&mut self, t: TokenType) -> Option<()> {
        if self.peek_token_is(t) {
            self.ignore_next()
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

    fn peek_precedence(&mut self) -> Precedence {
        if let Some(peeked) = self.l.peek() {
            if let Ok(tok) = peeked {
                if let Some(&p) = self.precedences.get(&tok.token_type) {
                    return p;
                }
            }
        }
        Precedence::LOWEST
    }

    fn curr_precedence(&mut self) -> Precedence {
        if let Some(&p) = self.precedences.get(&self.tok.token_type) {
            p
        } else {
            Precedence::LOWEST
        }
    }

    fn register_prefix(&mut self, tt: TokenType, func: fn(&mut Self) -> Option<Expr>) {
        self.prefix_parse_fns.insert(tt, func);
    }

    fn register_infix(&mut self, tt: TokenType, func: fn(&mut Self, Expr) -> Option<Expr>) {
        self.infix_parse_fns.insert(tt, func);
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::Node, lexer::lexer::Lexer};

    use super::*;
    use std::io::{self, Read};

    type FileByte = std::result::Result<u8, io::Error>;

    fn parse<I: Iterator<Item = FileByte>>(input: I) -> Result<Program> {
        let l = Lexer::new(input.peekable())?;
        let mut p = Parser::new(l.peekable())?;
        let program = p.parse()?;

        check_parser_errors(p)?;

        Ok(program)
    }

    fn test_let_statement(stmt: &Stmt, expected_ident: &String, expected_expr: &Expr) -> Result<()> {
        assert_eq!("let", stmt.token_literal());

        let let_stmt = match stmt {
            Stmt::Let(l) => l,
            _ => panic!("Expected let statement. Got {:?}", stmt),
        };

        assert_eq!(*expected_ident, let_stmt.name.value);
        test_literal_expression(expected_expr, &let_stmt.value)
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

    fn test_integer_literal(expected: i128, expr: &Expr) -> Result<()> {
        if let Expr::Int(x) = expr {
            assert_eq!(expected, x.value);
            assert_eq!(format!("{}", expected), x.token_literal());
            Ok(())
        } else {
            Err(Error::new(format!("Expression {:?} was not an Integer literal.", expr)))
        }
    }

    fn test_identifier(expected: &String, expr: &Expr) -> Result<()> {
        if let Expr::Ident(x) = expr {
            assert_eq!(*expected, x.value);
            assert_eq!(*expected, x.token_literal());
            Ok(())
        } else {
            Err(Error::new(format!("Expression {:?} was not an identifier.", expr)))
        }
    }

    fn test_boolean(expected: bool, expr: &Expr) -> Result<()> {
        if let Expr::Bool(x) = expr {
            assert_eq!(expected, x.value);
            assert_eq!(format!("{}", expected), x.token_literal());
            Ok(())
        } else {
            Err(Error::new(format!("Expression {:?} was not a boolean.", expr)))
        }
    }

    fn test_literal_expression(expected: &Expr, expr: &Expr) -> Result<()> {
        match expected {
            Expr::Int(x) => test_integer_literal(x.value, expr),
            Expr::Ident(x) => test_identifier(&x.value, expr),
            Expr::Bool(x) => test_boolean(x.value, expr),
            _ => Err(Error::new(format!("Expression {:?} is not a literal expression.", expected)))
        }
    }

    fn test_infix_expression(actual: &Expr, left: &Expr, operator: String, right: &Expr) -> Result<()> {
        if let Expr::In(x) = actual {
            test_literal_expression(left, &x.left)?;
            assert_eq!(operator, x.operator);
            test_literal_expression(right, &x.right)
        } else {
            Err(Error::new(format!("Expression `{}` was not an infix expression.", actual)))
        }
    }

    fn i_to_expr(i: i128) -> Expr {
        Expr::Int(
            IntegerLiteral {
                token: Token { literal: format!("{}", i), token_type: TokenType::INT },
                value: i,
            }
        )
    }

    fn b_to_expr(i: bool) -> Expr {
        Expr::Bool(
            BooleanLiteral {
                token: Token { literal: format!("{}", i), token_type: if i { TokenType::TRUE } else { TokenType::FALSE } },
                value: i,
            }
        )
    }

    fn l_to_expr(i: String) -> Expr {
        Expr::Ident(
            Identifier {
                token: Token { literal: i.clone(), token_type: TokenType::IDENT },
                value: i,
            }
        )
    }

    #[test]
    fn test_let_statements() -> Result<()> {
        let input = br###"
            let x = 5;
            let y = true;
            let foobar = y;
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(3, program.stmts.len());

        let tests = vec![
            ("x".to_string(), i_to_expr(5)),
            ("y".to_string(), b_to_expr(true)),
            ("foobar".to_string(), l_to_expr("y".to_string())),
        ];

        for (i, t) in tests.iter().enumerate() {
            if let Some(stmt) = program.stmts.get(i) {
                test_let_statement(stmt, &t.0, &t.1)?;
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
            let 838383;
        "###.to_vec();

        let l = Lexer::new(input.bytes().peekable())?;
        let mut p = Parser::new(l.peekable())?;
        p.parse()?;


        let tests = vec![
            (TokenType::ASSIGN, TokenType::INT),
            (TokenType::IDENT, TokenType::INT),
        ];

        for (i, err) in p.errors.iter().enumerate() {
            let test = tests.get(i).unwrap();

            let msg = format!("Expected next token to be {:?}, got {:?} instead.", test.0, test.1);
            assert_eq!(msg, *err);
        }

        assert_eq!(2, p.errors.len());

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

    #[test]
    fn test_identifier_expressions() -> Result<()> {
        let input = br###"
            foobar;
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(1, program.stmts.len());

        let stmt = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            x
        } else {
            panic!("Program statement was not an expression statement.");
        };

        test_identifier(&"foobar".to_string(), &stmt.expr)
    }

    #[test]
    fn test_integer_literal_expressions() -> Result<()> {
        let input = br###"
            5;
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(1, program.stmts.len());

        let stmt = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            x
        } else {
            panic!("Program statement was not an expression statement.");
        };

        test_integer_literal(5, &stmt.expr)?;

        Ok(())
    }

    #[test]
    fn test_boolean_expressions() -> Result<()> {
        let input = br###"
            true;
            false;
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(2, program.stmts.len());

        if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            test_boolean(true, &x.expr)?;
        } else {
            panic!("Program statement was not a boolean statement.");
        };

        if let Stmt::Expression(x) = program.stmts.get(1).unwrap() {
            test_boolean(false, &x.expr)?;
        } else {
            panic!("Program statement was not a boolean statement.");
        };

        Ok(())
    }

    #[test]
    fn test_parsing_prefix_expressions() -> Result<()> {
        let tests = vec![
            ("!5;".to_string(), "!".to_string(), i_to_expr(5)),
            ("-15;".to_string(), "-".to_string(), i_to_expr(15)),
            ("!true;".to_string(), "!".to_string(), b_to_expr(true)),
            ("!false;".to_string(), "!".to_string(), b_to_expr(false)),
        ];

        for tt in tests {
            let program = parse(tt.0.into_bytes().bytes())?;
            assert_eq!(1, program.stmts.len());

            let stmt = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
                x
            } else {
                panic!("Program statement was not an expression statement.");
            };

            if let Expr::Pre(expr) = &stmt.expr {
                assert_eq!(tt.1, expr.operator);
                test_literal_expression(&tt.2, &expr.right)?;
            } else {
                panic!("Expression `{}` was not a Prefix expression.", stmt.expr);
            };
        };

        Ok(())
    }

    #[test]
    fn test_parsing_infix_expressions() -> Result<()> {
        let tests = vec![
            ("5 + 5;".to_string(), i_to_expr(5), "+".to_string(), i_to_expr(5)),
            ("5 - 5;".to_string(), i_to_expr(5), "-".to_string(), i_to_expr(5)),
            ("5 * 5;".to_string(), i_to_expr(5), "*".to_string(), i_to_expr(5)),
            ("5 / 5;".to_string(), i_to_expr(5), "/".to_string(), i_to_expr(5)),
            ("5 > 5;".to_string(), i_to_expr(5), ">".to_string(), i_to_expr(5)),
            ("5 < 5;".to_string(), i_to_expr(5), "<".to_string(), i_to_expr(5)),
            ("5 == 5;".to_string(), i_to_expr(5), "==".to_string(), i_to_expr(5)),
            ("5 != 5;".to_string(), i_to_expr(5), "!=".to_string(), i_to_expr(5)),
            ("true == true".to_string(), b_to_expr(true), "==".to_string(), b_to_expr(true)),
            ("true != false".to_string(), b_to_expr(true), "!=".to_string(), b_to_expr(false)),
            ("false == false".to_string(), b_to_expr(false), "==".to_string(), b_to_expr(false)),
        ];

        for tt in tests {
            let program = parse(tt.0.into_bytes().bytes())?;
            assert_eq!(1, program.stmts.len());

            let stmt = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
                x
            } else {
                panic!("Program statement was not an expression statement.");
            };

            test_infix_expression(&stmt.expr, &tt.1, tt.2, &tt.3)?;
        };

        Ok(())
    }

    #[test]
    fn test_operator_precedence_parsing() -> Result<()> {
        let tests = vec![
            ("-a * b".to_string(), "((-a) * b)".to_string()),
            ("!-a".to_string(), "(!(-a))".to_string()),
            ("a + b + c".to_string(), "((a + b) + c)".to_string()),
            ("a + b - c".to_string(), "((a + b) - c)".to_string()),
            ("a * b * c".to_string(), "((a * b) * c)".to_string()),
            ("a * b / c".to_string(), "((a * b) / c)".to_string()),
            ("a + b / c".to_string(), "(a + (b / c))".to_string()),
            ("a + b * c + d / e - f".to_string(), "(((a + (b * c)) + (d / e)) - f)".to_string()),
            ("3 + 4; -5 * 5".to_string(), "(3 + 4)((-5) * 5)".to_string()),
            ("5 > 4 == 3 < 4".to_string(), "((5 > 4) == (3 < 4))".to_string()),
            ("5 < 4 != 3 > 4".to_string(), "((5 < 4) != (3 > 4))".to_string()),
            ("3 + 4 * 5 == 3 * 1 + 4 * 5".to_string(), "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))".to_string()),
            ("true".to_string(), "true".to_string()),
            ("false".to_string(), "false".to_string()),
            ("3 > 5 == false".to_string(), "((3 > 5) == false)".to_string()),
            ("3 < 5 == true".to_string(), "((3 < 5) == true)".to_string()),
            ("1 + (2 + 3) + 4".to_string(), "((1 + (2 + 3)) + 4)".to_string()),
            ("(5 + 5) * 2".to_string(), "((5 + 5) * 2)".to_string()),
            ("2 / (5 + 5)".to_string(), "(2 / (5 + 5))".to_string()),
            ("-(5 + 5)".to_string(), "(-(5 + 5))".to_string()),
            ("!(true == true)".to_string(), "(!(true == true))".to_string()),
            ("a + add(b * c) + d".to_string(), "((a + add((b * c))) + d)".to_string()),
            ("add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))".to_string(), "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))".to_string()),
            ("add(a + b + c * d / f + g)".to_string(), "add((((a + b) + ((c * d) / f)) + g))".to_string()),
        ];

        for tt in tests {
            let program = parse(tt.0.as_bytes().bytes())?;
            assert_eq!(tt.1, format!("{}", program));
        }

        Ok(())
    }

    #[test]
    fn test_parsing_if_expressions() -> Result<()> {
        let input = br###"
            if (x < y) { x }
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(1, program.stmts.len());

        let if_expr = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            if let Expr::If(i) = &x.expr {
                i
            } else {
                panic!("Program statement was not an if expression.");
            }
        } else {
            panic!("Program statement was not a expression statement.");
        };

        test_infix_expression(&if_expr.condition, &l_to_expr("x".to_string()), "<".to_string(), &l_to_expr("y".to_string()))?;

        let conseq = &if_expr.consequence;

        assert_eq!(1, conseq.stmts.len());

        if let Stmt::Expression(x) = conseq.stmts.get(0).unwrap() {
            test_identifier(&"x".to_string(), &x.expr)?;
        } else {
            panic!("Consequence statement was not an expression statement.");
        }

        assert!(if_expr.alternative.is_none());

        Ok(())
    }

    #[test]
    fn test_parsing_if_else_expressions() -> Result<()> {
        let input = br###"
            if (x < y) { x } else { y }
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(1, program.stmts.len());

        let if_expr = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            if let Expr::If(i) = &x.expr {
                i
            } else {
                panic!("Program statement was not an if expression.");
            }
        } else {
            panic!("Program statement was not a expression statement.");
        };

        test_infix_expression(&if_expr.condition, &l_to_expr("x".to_string()), "<".to_string(), &l_to_expr("y".to_string()))?;

        let conseq = &if_expr.consequence;

        assert_eq!(1, conseq.stmts.len());

        if let Stmt::Expression(x) = conseq.stmts.get(0).unwrap() {
            test_identifier(&"x".to_string(), &x.expr)?;
        } else {
            panic!("Consequence statement was not an expression statement.");
        }

        let alt = if_expr.alternative.as_ref().unwrap();

        assert_eq!(1, alt.stmts.len());

        if let Stmt::Expression(x) = alt.stmts.get(0).unwrap() {
            test_identifier(&"y".to_string(), &x.expr)?;
        } else {
            panic!("Alternative statement was not an expression statement.");
        }

        Ok(())
    }

    #[test]
    fn test_parsing_function_literals() -> Result<()> {
        let input = br###"
            fn(x, y) { x + y }
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(1, program.stmts.len());

        let fn_expr = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            if let Expr::Fn(f) = &x.expr {
                f
            } else {
                panic!("Program statement was not a Function expression.");
            }
        } else {
            panic!("Program statement was not a expression statement.");
        };

        assert_eq!(2, fn_expr.params.len());

        test_literal_expression(&l_to_expr("x".to_string()), &Expr::Ident(fn_expr.params.get(0).unwrap().clone()))?;
        test_literal_expression(&l_to_expr("y".to_string()), &Expr::Ident(fn_expr.params.get(1).unwrap().clone()))?;

        assert_eq!(1, fn_expr.body.stmts.len());

        if let Stmt::Expression(x) = fn_expr.body.stmts.get(0).unwrap() {
            test_infix_expression(&x.expr, &l_to_expr("x".to_string()), "+".to_string(), &l_to_expr("y".to_string()))?;
        } else {
            panic!("Body statement was not an expression statement.");
        }

        Ok(())
    }

    #[test]
    fn test_function_param_parsing() -> Result<()> {
        let tests = vec![
            ("fn() {};".to_string(), Vec::new()),
            ("fn(x) {};".to_string(), vec!["x".to_string()]),
            ("fn(x, y, z) {};".to_string(), vec!["x".to_string(), "y".to_string(), "z".to_string()]),
        ];

        for tt in tests {
            let program = parse(tt.0.as_bytes().bytes())?;
            let fn_expr = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
                if let Expr::Fn(f) = &x.expr {
                    f
                } else {
                    panic!("Program statement was not a Function expression.");
                }
            } else {
                panic!("Program statement was not a expression statement.");
            };

            assert_eq!(tt.1.len(), fn_expr.params.len());

            for (i, ident) in tt.1.iter().enumerate() {
                test_identifier(ident, &Expr::Ident(fn_expr.params.get(i).unwrap().clone()))?;
            }
        }

        Ok(())
    }

    #[test]
    fn test_fn_call_parsing() -> Result<()> {
        let input = br###"
            add(1, 2 * 3, 4 + 5);
        "###.to_vec();

        let program = parse(input.bytes())?;
        assert_eq!(1, program.stmts.len());

        let call_expr = if let Stmt::Expression(x) = program.stmts.get(0).unwrap() {
            if let Expr::Call(f) = &x.expr {
                f
            } else {
                panic!("Program statement was not a Function expression.");
            }
        } else {
            panic!("Program statement was not a expression statement.");
        };

        assert_eq!(3, call_expr.args.len());

        test_identifier(&"add".to_string(), &call_expr.function)?;

        test_literal_expression(&i_to_expr(1), call_expr.args.get(0).unwrap())?;
        test_infix_expression(call_expr.args.get(1).unwrap(), &i_to_expr(2), "*".to_string(), &i_to_expr(3))?;
        test_infix_expression(call_expr.args.get(2).unwrap(), &i_to_expr(4), "+".to_string(), &i_to_expr(5))?;

        Ok(())
    }
}

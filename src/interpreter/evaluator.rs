use crate::{
    error::Error,
    interpreter::object::*,
    ast::*,
};

type Result<T> = std::result::Result<T, Error>;

pub fn eval(node: MNode) -> Result<MObject> {
    match node {
        MNode::Prog(x) => {
            eval_statements(x.stmts)
        },
        MNode::Stmt(stmt) => {
            match stmt {
                Stmt::Expression(expr) => eval(MNode::Expr(expr.expr)),
                _ => Err(Error::new(format!("Stmt: {:?} is not supported yet.", stmt))),
            }
        },
        MNode::Expr(expr) => {
            match expr {
                Expr::Int(i) => Ok(MObject::Int(Integer { value: i.value })),
                _ => Err(Error::new(format!("Expr: {:?} is not supported yet.", expr)))
            }
        },
    }
}

fn eval_statements(stmts: Vec<Stmt>) -> Result<MObject> {
    let mut result = if let Some(stmt) = stmts.get(0) {
        eval(MNode::Stmt(stmt.clone()))
    } else {
        return Err(Error::new("No statements in statement list.".to_string()))
    };

    for stmt in stmts.iter().skip(1) {
        // TODO: consider taking ownership and removing the stmts from the Vec
        result = eval(MNode::Stmt(stmt.clone()));
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexer::{lexer::Lexer, token::Token}, parser::parser::Parser};

    use std::io::Read;

    type Result<T> = std::result::Result<T, Error>;


    fn test_eval(input: String) -> Result<MObject> {
        let lex = Lexer::new(input.as_bytes().bytes().peekable())?;
        let mut parser = Parser::new(lex.peekable())?;
        let program = parser.parse()?;

        check_parser_errors(parser)?;

        eval(MNode::Prog(program))
    }

    fn check_parser_errors<I: Iterator<Item = Result<Token>>>(p: Parser<I>) -> Result<()> {
        let errors = p.errors();

        if errors.is_empty() {
            return Ok(());
        }

        let mut msg = format!("The Parser had {} errors:\n", errors.len());

        for e in errors {
            msg.push_str(&e);
            msg.push('\n');
        }

        Err(Error::new(msg))
    }

    fn test_integer_obj(expected: i128, actual: MObject) -> Result<()> {
        if let MObject::Int(m_int) = actual {
            assert_eq!(expected, m_int.value);
            Ok(())
        } else {
            Err(Error::new(format!("MObject wasn't an integer, it was {:?}.", actual)))
        }
    }

    #[test]
    fn test_eval_integer_expressions() -> Result<()> {
        let tests = vec![
            ("5".to_string(), 5),
            ("10".to_string(), 10),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        }

        Ok(())
    }
}

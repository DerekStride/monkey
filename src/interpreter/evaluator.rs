use crate::{
    error::Error,
    interpreter::object::*,
    ast::*,
};

type Result<T> = std::result::Result<T, Error>;

const TRUE: MObject = MObject::Bool(Boolean { value: true });
const FALSE: MObject = MObject::Bool(Boolean { value: false });
const NULL: MObject = MObject::Null;

#[inline]
fn native_bool_to_boolean(b: bool) -> MObject {
    if b { TRUE } else { FALSE }
}

#[inline]
fn is_truthy(o: MObject) -> bool {
    match o {
        TRUE => true,
        FALSE => false,
        NULL => false,
        _ => true,
    }
}

pub fn eval(node: MNode) -> Result<MObject> {
    match node {
        MNode::Prog(x) => {
            eval_statements(x.stmts)
        },
        MNode::Stmt(stmt) => {
            match stmt {
                Stmt::Expression(expr) => eval(MNode::Expr(expr.expr)),
                Stmt::Block(blk_stmt) => eval_statements(blk_stmt.stmts),
                _ => Err(Error::new(format!("Stmt: {:?} is not supported yet.", stmt))),
            }
        },
        MNode::Expr(expr) => {
            match expr {
                Expr::Int(i) => Ok(MObject::Int(Integer { value: i.value })),
                Expr::Bool(b) => Ok(native_bool_to_boolean(b.value)),
                Expr::Pre(prefix) => {
                    let right = eval(MNode::Expr(*prefix.right))?;
                    eval_prefix_expression(prefix.operator, right)
                },
                Expr::In(infix) => {
                    let left = eval(MNode::Expr(*infix.left))?;
                    let right = eval(MNode::Expr(*infix.right))?;
                    eval_infix_expression(left, infix.operator, right)
                },
                Expr::If(if_expr) => eval_if_expression(if_expr),
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

fn eval_prefix_expression(op: String, obj: MObject) -> Result<MObject> {
    match op.as_str() {
        "!" => Ok(eval_bang_operator_expression(obj)),
        "-" => Ok(eval_minus_prefix_operator_expression(obj)),
        _ => Ok(NULL),
    }
}

fn eval_bang_operator_expression(obj: MObject) -> MObject {
    match obj {
        TRUE => FALSE,
        FALSE => TRUE,
        NULL => TRUE,
        _ => FALSE,
    }
}

fn eval_minus_prefix_operator_expression(obj: MObject) -> MObject {
    if let MObject::Int(m_int) = obj {
        MObject::Int(Integer { value: -m_int.value })
    } else {
        NULL
    }
}

fn eval_infix_expression(left: MObject, op: String, right: MObject) -> Result<MObject> {
    if let MObject::Int(left_int) = left {
        if let MObject::Int(right_int) = right {
            return eval_integer_infix_operator(left_int.value, op, right_int.value);
        }
    } else if let MObject::Bool(left_bool) = left {
        if let MObject::Bool(right_bool) = right {
            return eval_boolean_infix_operator(left_bool.value, op, right_bool.value);
        }
    }
    Err(Error::new(format!("Left and right operands must be either both booleans or both integers, they were left: {}, op: {}, right: {}", left, op, right)))
}

fn eval_integer_infix_operator(left: i128, op: String, right: i128) -> Result<MObject> {
    let result = match op.as_str() {
        "+" => MObject::Int(Integer { value: left + right }),
        "-" => MObject::Int(Integer { value: left - right }),
        "*" => MObject::Int(Integer { value: left * right }),
        "/" => MObject::Int(Integer { value: left / right }),
        "<" => native_bool_to_boolean(left < right),
        ">" => native_bool_to_boolean(left > right),
        "==" => native_bool_to_boolean(left == right),
        "!=" => native_bool_to_boolean(left != right),
        _ => return Err(Error::new(format!("The operator: '{}' is not supported.", op))),
    };
    Ok(result)
}

fn eval_boolean_infix_operator(left: bool, op: String, right: bool) -> Result<MObject> {
    let result = match op.as_str() {
        "==" => native_bool_to_boolean(left == right),
        "!=" => native_bool_to_boolean(left != right),
        _ => return Err(Error::new(format!("The operator: '{}' is not supported.", op))),
    };
    Ok(result)
}

fn eval_if_expression(if_expr: IfExpression) -> Result<MObject> {
    let condition = eval(MNode::Expr(*if_expr.condition))?;

    if is_truthy(condition) {
        eval(MNode::Stmt(Stmt::Block(if_expr.consequence)))
    } else if let Some(alternative) = if_expr.alternative {
        eval(MNode::Stmt(Stmt::Block(alternative)))
    } else {
        Ok(NULL)
    }
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

    fn test_boolean_obj(expected: bool, actual: MObject) -> Result<()> {
        if let MObject::Bool(m_bool) = actual {
            assert_eq!(expected, m_bool.value);
            Ok(())
        } else {
            Err(Error::new(format!("MObject wasn't a boolean, it was {:?}.", actual)))
        }
    }

    #[test]
    fn test_eval_integer_expressions() -> Result<()> {
        let tests = vec![
            ("5".to_string(), 5),
            ("10".to_string(), 10),
            ("-5".to_string(), -5),
            ("-10".to_string(), -10),
            ("5 + 5 + 5 + 5 - 10".to_string(), 10),
            ("2 * 2 * 2 * 2 * 2".to_string(), 32),
            ("-50 + 100 + -50".to_string(), 0),
            ("5 * 2 + 10".to_string(), 20),
            ("5 + 2 * 10".to_string(), 25),
            ("20 + 2 * -10".to_string(), 0),
            ("50 / 2 * 2 + 10".to_string(), 60),
            ("2 * (5 + 10)".to_string(), 30),
            ("3 * 3 * 3 + 10".to_string(), 37),
            ("3 * (3 * 3) + 10".to_string(), 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10".to_string(), 50),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        }

        Ok(())
    }

    #[test]
    fn test_eval_boolean_expressions() -> Result<()> {
        let tests = vec![
            ("true".to_string(), true),
            ("false".to_string(), false),
            ("1 < 2".to_string(), true),
            ("1 > 2".to_string(), false),
            ("1 < 1".to_string(), false),
            ("1 > 1".to_string(), false),
            ("1 == 1".to_string(), true),
            ("1 != 1".to_string(), false),
            ("1 == 2".to_string(), false),
            ("1 != 2".to_string(), true),
            ("true == true".to_string(), true),
            ("false == false".to_string(), true),
            ("true == false".to_string(), false),
            ("true != false".to_string(), true),
            ("false != true".to_string(), true),
            ("(1 < 2) == true".to_string(), true),
            ("(1 < 2) == false".to_string(), false),
            ("(1 > 2) == true".to_string(), false),
            ("(1 > 2) == false".to_string(), true),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_boolean_obj(tt.1, evaluated)?;
        }

        Ok(())
    }

    #[test]
    fn test_bang_operator() -> Result<()> {
        let tests = vec![
            ("!true".to_string(), false),
            ("!false".to_string(), true),
            ("!5".to_string(), false),
            ("!!true".to_string(), true),
            ("!!false".to_string(), false),
            ("!!5".to_string(), true),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_boolean_obj(tt.1, evaluated)?;
        }

        Ok(())
    }

    #[test]
    fn test_if_else_expressions() -> Result<()> {
        let tests = vec![
            ("if (true) { 10 }".to_string(), 10),
            ("if (1) { 10 }".to_string(), 10),
            ("if (1 < 2) { 10 }".to_string(), 10),
            ("if (1 > 2) { 10 } else { 20 }".to_string(), 20),
            ("if (1 < 2) { 10 } else { 20 }".to_string(), 10),
        ];

        let nil_tests = vec![
            ("if (false) { 10 }".to_string(), NULL),
            ("if (1 > 2) { 10 }".to_string(), NULL),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        }

        for tt in nil_tests {
            let evaluated = test_eval(tt.0)?;
            assert_eq!(NULL, evaluated);
        }

        Ok(())
    }
}

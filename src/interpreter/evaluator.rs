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

#[inline]
fn new_error(value: String) -> MObject {
    MObject::Err(
        MError {
            value,
        }
    )
}

pub fn eval(node: MNode, env: &mut Environment) -> Result<MObject> {
    match node {
        MNode::Prog(x) => {
            eval_program(x.stmts, env)
        },
        MNode::Stmt(stmt) => {
            match stmt {
                Stmt::Expression(expr) => eval(MNode::Expr(expr.expr), env),
                Stmt::Block(blk_stmt) => eval_block_statements(blk_stmt.stmts, env),
                Stmt::Let(let_stmt) => {
                    let value = eval(MNode::Expr(let_stmt.value), env)?;
                    if let MObject::Err(_) = value { return Ok(value); };
                    env.insert(let_stmt.name.value.clone(), value.clone());

                    Ok(value)
                },
                Stmt::Return(ret) => {
                    let val = eval(MNode::Expr(ret.retval), env)?;
                    if let MObject::Err(_) = val { return Ok(val); };

                    Ok(MObject::Return(ReturnValue { value: Box::new(val) }))
                },
            }
        },
        MNode::Expr(expr) => {
            match expr {
                Expr::Int(i) => Ok(MObject::Int(Integer { value: i.value })),
                Expr::Bool(b) => Ok(native_bool_to_boolean(b.value)),
                Expr::Pre(prefix) => {
                    let right = eval(MNode::Expr(*prefix.right), env)?;
                    if let MObject::Err(_) = right { return Ok(right); };

                    eval_prefix_expression(prefix.operator, right)
                },
                Expr::In(infix) => {
                    let left = eval(MNode::Expr(*infix.left), env)?;
                    if let MObject::Err(_) = left { return Ok(left); };

                    let right = eval(MNode::Expr(*infix.right), env)?;
                    if let MObject::Err(_) = right { return Ok(right); };

                    eval_infix_expression(left, infix.operator, right)
                },
                Expr::If(if_expr) => eval_if_expression(if_expr, env),
                Expr::Ident(ident) => eval_identifier_expression(ident, env),
                Expr::Fn(func) => {
                    Ok(
                        MObject::Fn(
                            Function {
                                params: func.params,
                                body: func.body,
                                env: env.clone(),
                            }
                        )
                    )
                },
                Expr::Call(func_call) => {
                    let function = eval(MNode::Expr(*func_call.function), env)?;
                    if let MObject::Err(_) = function { return Ok(function); };

                    let mut args = eval_expressions(func_call.args, env)?;

                    if args.len() == 1 {
                        if let Some(value) = args.get(0) {
                            if let MObject::Err(_) = value {
                                return Ok(value.clone());
                            };
                        };
                    };

                    apply_function(function, &mut args)
                },
                _ => Err(Error::new(format!("Expression: {} not supported", expr))),
            }
        },
    }
}

fn eval_program(stmts: Vec<Stmt>, env: &mut Environment) -> Result<MObject> {
    let mut result = if let Some(stmt) = stmts.get(0) {
        eval(MNode::Stmt(stmt.clone()), env)?
    } else {
        return Err(Error::new("No statements in statement list.".to_string()))
    };
    if let MObject::Return(retval) = result {
        return Ok(*retval.value);
    } else if let MObject::Err(_) = result {
        return Ok(result);
    };

    for stmt in stmts.iter().skip(1) {
        // TODO: consider taking ownership and removing the stmts from the Vec
        result = eval(MNode::Stmt(stmt.clone()), env)?;

        if let MObject::Return(retval) = result {
            return Ok(*retval.value);
        } else if let MObject::Err(_) = result {
            return Ok(result);
        };
    }

    Ok(result)

}

fn eval_block_statements(stmts: Vec<Stmt>, env: &mut Environment) -> Result<MObject> {
    let mut result = if let Some(stmt) = stmts.get(0) {
        eval(MNode::Stmt(stmt.clone()), env)?
    } else {
        return Err(Error::new("No statements in statement list.".to_string()))
    };
    if let MObject::Return(_) = result {
        return Ok(result);
    } else if let MObject::Err(_) = result {
        return Ok(result);
    };

    for stmt in stmts.iter().skip(1) {
        // TODO: consider taking ownership and removing the stmts from the Vec
        result = eval(MNode::Stmt(stmt.clone()), env)?;

        if let MObject::Return(_) = result {
            return Ok(result);
        } else if let MObject::Err(_) = result {
            return Ok(result);
        };
    }

    Ok(result)
}

fn eval_expressions(exprs: Vec<Expr>, env: &mut Environment) -> Result<Vec<MObject>> {
    let mut results = Vec::new();

    for expr in exprs {
        let obj = eval(MNode::Expr(expr), env)?;
        if let MObject::Err(_) = obj { return Ok(vec![obj]); };

        results.push(obj);
    }

    Ok(results)
}

fn apply_function(obj: MObject, args: &mut Vec<MObject>) -> Result<MObject> {
    let function = if let MObject::Fn(f) = obj {
        f
    } else {
        return Ok(new_error(format!("not a function: {}", obj)));
    };

    let Function { params, body, env } = function;

    let mut extended_env = match extend_function_env(params, args, env) {
        Ok(x) => x,
        Err(e) => return Ok(new_error(format!("{}", e))),
    };

    let evaluated = eval(MNode::Stmt(Stmt::Block(body)), &mut extended_env)?;

    if let MObject::Return(retval) = evaluated {
        Ok(*retval.value)
    } else {
        Ok(evaluated)
    }
}

fn extend_function_env(params: Vec<Identifier>, args: &mut Vec<MObject>, env: Environment) -> Result<Environment> {
    let mut env = Environment::enclose(env);
    if params.len() != args.len() {
        return Err(Error::new(format!("Expected {} parameters, got {}.", params.len(), args.len())));
    };
    args.reverse();

    for param in params.iter() {
        let arg = args.pop().unwrap();
        env.insert(param.value.clone(), arg);
    }

    Ok(env)
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
        new_error(format!("unknown operator: -{}", obj))
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
    Ok(new_error(format!("type mismatch: {} {} {}", left, op, right)))
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
        _ => new_error(format!("unknown operator: {} {} {}", left, op, right)),
    };
    Ok(result)
}

fn eval_boolean_infix_operator(left: bool, op: String, right: bool) -> Result<MObject> {
    let result = match op.as_str() {
        "==" => native_bool_to_boolean(left == right),
        "!=" => native_bool_to_boolean(left != right),
        _ => new_error(format!("unknown operator: {} {} {}", left, op, right)),
    };
    Ok(result)
}

fn eval_if_expression(if_expr: IfExpression, env: &mut Environment) -> Result<MObject> {
    let condition = eval(MNode::Expr(*if_expr.condition), env)?;

    if let MObject::Err(_) = condition {
        Ok(condition)
    } else if is_truthy(condition) {
        eval(MNode::Stmt(Stmt::Block(if_expr.consequence)), env)
    } else if let Some(alternative) = if_expr.alternative {
        eval(MNode::Stmt(Stmt::Block(alternative)), env)
    } else {
        Ok(NULL)
    }
}

fn eval_identifier_expression(ident: Identifier, env: &mut Environment) -> Result<MObject> {
    if let Some(v) = env.get(&ident.value) {
        Ok(v.clone())
    } else {
        Ok(new_error(format!("identifier not found: {}", ident.value)))
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
        let mut env = Environment::new();

        eval(MNode::Prog(program), &mut env)
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

    #[test]
    fn test_return_statements() -> Result<()> {
        let tests = vec![
            ("return 10;".to_string(), 10),
            ("return 10; 9;".to_string(), 10),
            ("return 2 * 5; 9;".to_string(), 10),
            ("9; return 2 * 5; 9;".to_string(), 10),
            ("if (10 > 1) {
                if (10 > 1) {
                    return 10;
                }

                return 1;
            }".to_string(), 10),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        }

        Ok(())
    }

    #[test]
    fn test_error_handling() -> Result<()> {
        let tests = vec![
            ( "5 + true;".to_string(), "type mismatch: 5 + true".to_string()),
            ( "5 + true; 5;".to_string(), "type mismatch: 5 + true".to_string()),
            ( "-true".to_string(), "unknown operator: -true".to_string()),
            ( "true + false;".to_string(), "unknown operator: true + false".to_string()),
            ( "5; true + false; 5".to_string(), "unknown operator: true + false".to_string()),
            ( "if (10 > 1) { true + false; }".to_string(), "unknown operator: true + false".to_string()),
            ("if (10 > 1) {
                if (10 > 1) {
                    return true + false;
                }

                return 1;
            }".to_string(), "unknown operator: true + false".to_string()),
            ("foobar".to_string(), "identifier not found: foobar".to_string()),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;

            if let MObject::Err(e) = evaluated {
                assert_eq!(tt.1, e.value);
            } else {
                panic!("Expected Error: {}, got: {}", tt.1, evaluated);
            }
        };

        Ok(())
    }

    #[test]
    fn test_let_statements() -> Result<()> {
        let tests = vec![
            ("let a = 5; a;".to_string(), 5),
            ("let a = 5 * 5; a;".to_string(), 25),
            ("let a = 5; let b = a; b;".to_string(), 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;".to_string(), 15),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        };

        Ok(())
    }

    #[test]
    fn test_function_objects() -> Result<()> {
        let input = "fn(x) { x + 2; };".to_string();
        let evaluated = test_eval(input)?;

        if let MObject::Fn(func) = evaluated {
            assert_eq!(1, func.params.len());
            assert_eq!("x", func.params.get(0).unwrap().value);
            assert_eq!("(x + 2)", format!("{}", func.body));
        } else {
            panic!("Expected function, got: {}", evaluated);
        };

        Ok(())
    }

    #[test]
    fn test_function_application() -> Result<()> {
        let tests = vec![
            ("let identity = fn(x) { x; }; identity(5);".to_string(), 5),
            ("let identity = fn(x) { return x; }; identity(5);".to_string(), 5),
            ("let double = fn(x) { x * 2; }; double(5);".to_string(), 10),
            ("let add = fn(x, y) { x + y; }; add(5, 5);".to_string(), 10),
            ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));".to_string(), 20),
            ("fn(x) { x; }(5)".to_string(), 5),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        };

        Ok(())
    }

    #[test]
    fn test_closures() -> Result<()> {
        let input = "
            let newAdder = fn(x) {
                fn(y) { x + y };
            };

        let addTwo = newAdder(2);
        addTwo(2);".to_string();

        test_integer_obj(4, test_eval(input)?)
    }
}

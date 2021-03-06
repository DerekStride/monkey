use std::{collections::HashMap, cell::RefCell, rc::Rc};

use crate::{
    error::{Result, Error},
    object::*,
    builtin::Builtin,
    interpreter::environment::Environment,
    ast::*, lexer::{token::Token, token_type::TokenType},
};

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

fn is_macro_definition(statement: &Stmt) -> bool {
    match statement {
        Stmt::Let(stmt) => {
            match stmt.value {
                Expr::Macro(_) => true,
                _ => false,
            }
        },
        _ => false,
    }
}

fn add_macro(statement: &Stmt, env: Rc<RefCell<Environment>>) {
    match statement {
        Stmt::Let(stmt) => {
            match stmt.value {
                Expr::Macro(ref x) => {
                    let macro_lit = Macro {
                        params: x.params.clone(),
                        body: x.body.clone(),
                        env: env.clone(),
                    };
                    let mut e = env.borrow_mut();
                    e.insert(stmt.name.value.clone(), MObject::Macro(macro_lit));
                },
                _ => {},
            }
        },
        _ => {},
    };
}

pub fn define_macros(program: &mut Program, env: Rc<RefCell<Environment>>) {
    let mut definitions = vec![];

    for (i, statement) in program.stmts.iter().enumerate() {
        if is_macro_definition(statement) {
            add_macro(statement, env.clone());
            definitions.push(i);
        }
    }

    for i in definitions {
        program.stmts.remove(i);
    }
}

fn is_macro_call(call: &FnCall, env: Rc<RefCell<Environment>>) -> Option<Macro> {
    if let Expr::Ident(ident) = &*call.function {
        let env = env.borrow();
        if let Some(obj) = env.get(&ident.value) {
            if let MObject::Macro(m) = obj.as_ref() {
                return Some(m.clone());
            };
        };
    };
    None
}

fn quote_args(call: FnCall) -> Vec<Quote> {
    let mut args = vec![];

    for arg in call.args {
        args.push(Quote { node: MNode::Expr(arg) });
    };

    args
}

fn extend_macro_env(mac: Macro, args: Vec<Quote>) -> Rc<RefCell<Environment>> {
    let extended = Environment::enclose(mac.env);
    {
        let mut env = extended.borrow_mut();

        for (i, param) in mac.params.iter().enumerate() {
            if let Some(arg) = args.get(i) {
                env.insert(param.value.clone(), MObject::Quote(arg.clone()));
            };
        };
    }

    extended
}

pub fn expand_macros(program: Program, env: Rc<RefCell<Environment>>) -> MNode {
    crate::ast::modify(MNode::Prog(program), env, |node: MNode, env: Rc<RefCell<Environment>>| -> MNode {
        match node {
            MNode::Expr(Expr::Call(ref c)) => {
                let mac = if let Some(m) = is_macro_call(c, env) {
                    m
                } else {
                    return node;
                };

                let args = quote_args(c.clone());
                let eval_env = extend_macro_env(mac.clone(), args);

                let evaluated = eval(MNode::Stmt(Stmt::Block(mac.body)), eval_env);

                if let Ok(MObject::Quote(q)) = evaluated {
                    return q.node;
                } else {
                    panic!("we only support return AST-nodes from macros");
                }
            },
            _ => return node,
        }
    })
}

pub fn eval(node: MNode, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    match node {
        MNode::Prog(x) => {
            eval_program(x.stmts, env)
        },
        MNode::Stmt(stmt) => {
            match stmt {
                Stmt::Expression(expr) => eval(MNode::Expr(expr.expr), env),
                Stmt::Block(blk_stmt) => eval_block_statements(blk_stmt.stmts, env),
                Stmt::Let(let_stmt) => {
                    let value = eval(MNode::Expr(let_stmt.value), env.clone())?;
                    if let MObject::Err(_) = value { return Ok(value); };
                    let mut env = env.borrow_mut();
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
                    let left = eval(MNode::Expr(*infix.left), env.clone())?;
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
                    if func_call.function.token_literal() == "quote" {
                        return quote(func_call.args.get(0), env);
                    };

                    let function = eval(MNode::Expr(*func_call.function), env.clone())?;
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
                Expr::Str(s) => Ok(MObject::Str(MString { value: s.value })),
                Expr::Array(a) => {
                    let elements = eval_expressions(a.elements, env)?;

                    if elements.len() == 1 {
                        if let Some(value) = elements.get(0) {
                            if let MObject::Err(_) = value {
                                return Ok(value.clone());
                            };
                        };
                    };

                    Ok(
                        MObject::Array(
                            MArray {
                                elements,
                            }
                        )
                    )
                },
                Expr::Index(i) => {
                    let left = eval(MNode::Expr(*i.left), env.clone())?;
                    if let MObject::Err(_) = left { return Ok(left); };

                    let index = eval(MNode::Expr(*i.index), env)?;
                    if let MObject::Err(_) = index { return Ok(index); };

                    eval_index_expression(left, index)
                },
                Expr::Hash(h) => {
                    eval_hash_literal_expression(h, env)
                },
                Expr::Macro(m) => {
                    Ok(new_error(format!("Macro not expanded: {}", m)))
                }
            }
        },
    }
}

fn eval_program(stmts: Vec<Stmt>, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    let mut result = if let Some(stmt) = stmts.get(0) {
        eval(MNode::Stmt(stmt.clone()), env.clone())?
    } else {
        return Ok(NULL)
    };
    if let MObject::Return(retval) = result {
        return Ok(*retval.value);
    } else if let MObject::Err(_) = result {
        return Ok(result);
    };

    for stmt in stmts.iter().skip(1) {
        // TODO: consider taking ownership and removing the stmts from the Vec
        result = eval(MNode::Stmt(stmt.clone()), env.clone())?;

        if let MObject::Return(retval) = result {
            return Ok(*retval.value);
        } else if let MObject::Err(_) = result {
            return Ok(result);
        };
    }

    Ok(result)

}

fn eval_block_statements(stmts: Vec<Stmt>, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    let mut result = if let Some(stmt) = stmts.get(0) {
        eval(MNode::Stmt(stmt.clone()), env.clone())?
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
        result = eval(MNode::Stmt(stmt.clone()), env.clone())?;

        if let MObject::Return(_) = result {
            return Ok(result);
        } else if let MObject::Err(_) = result {
            return Ok(result);
        };
    }

    Ok(result)
}

fn eval_expressions(exprs: Vec<Expr>, env: Rc<RefCell<Environment>>) -> Result<Vec<MObject>> {
    let mut results = Vec::new();

    for expr in exprs {
        let obj = eval(MNode::Expr(expr), env.clone())?;
        if let MObject::Err(_) = obj { return Ok(vec![obj]); };

        results.push(obj);
    }

    Ok(results)
}

fn apply_function(obj: MObject, args: &mut Vec<MObject>) -> Result<MObject> {
    if let MObject::Fn(f) = obj {
        let Function { params, body, env } = f;

        let extended_env = match extend_function_env(params, args, env) {
            Ok(x) => x,
            Err(e) => return Ok(new_error(format!("{}", e))),
        };

        let evaluated = eval(MNode::Stmt(Stmt::Block(body)), extended_env)?;

        if let MObject::Return(retval) = evaluated {
            Ok(*retval.value)
        } else {
            Ok(evaluated)
        }
    } else if let MObject::Builtin(b) = obj {
        match b {
            Builtin::Len(len) => len(args),
            Builtin::First(first) => first(args),
            Builtin::Last(last) => last(args),
            Builtin::Rest(rest) => rest(args),
            Builtin::Push(push) => push(args),
            Builtin::Puts(puts) => puts(args),
        }
    } else {
        Ok(new_error(format!("not a function: {}", obj)))
    }
}

fn extend_function_env(params: Vec<Identifier>, args: &mut Vec<MObject>, env: Rc<RefCell<Environment>>) -> Result<Rc<RefCell<Environment>>> {
    let enclosed = Environment::enclose(env);
    {
        if params.len() != args.len() {
            return Err(Error::new(format!("Expected {} parameters, got {}.", params.len(), args.len())));
        };
        args.reverse();

        let mut env = enclosed.borrow_mut();
        for param in params.iter() {
            let arg = args.pop().unwrap();
            env.insert(param.value.clone(), arg);
        }
    }

    Ok(enclosed)
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
    } else if let MObject::Str(ref left_str) = left {
        if let MObject::Str(right_str) = right {
            return eval_string_infix_operator(left_str.value.clone(), op, right_str.value);
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

fn eval_string_infix_operator(left: String, op: String, right: String) -> Result<MObject> {
    let result = match op.as_str() {
        "+" => MObject::Str(MString { value: left + &right }),
        _ => new_error(format!("unknown operator: {} {} {}", left, op, right)),
    };
    Ok(result)
}

fn eval_if_expression(if_expr: IfExpression, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    let condition = eval(MNode::Expr(*if_expr.condition), env.clone())?;

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

fn eval_identifier_expression(ident: Identifier, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    let env = env.borrow();
    if let Some(v) = env.get(&ident.value) {
        Ok(v.as_ref().clone())
    } else {
        Ok(new_error(format!("identifier not found: {}", ident.value)))
    }
}

fn eval_index_expression(left: MObject, index: MObject) -> Result<MObject> {
    if let MObject::Array(arr) = left {
        if let MObject::Int(i) = index {
            Ok(eval_array_index_expression(arr, i.value))
        } else {
            Ok(new_error(format!("index operator not supported: {}", index)))
        }
    } else if let MObject::Hash(h) = left {
        let hash_key = match index {
            MObject::Str(x) => HashKey::Str(x),
            MObject::Int(x) => HashKey::Int(x),
            MObject::Bool(x) => HashKey::Bool(x),
            _ => return Ok(new_error(format!("unusable as hash key: {}", index)))
        };

        match h.pairs.get(&hash_key) {
            Some(pair) => Ok(pair.value.clone()),
            None => Ok(NULL),
        }
    } else {
        Ok(new_error(format!("index operator not supported: {}", left)))
    }
}

fn eval_array_index_expression(arr: MArray, index: i128) -> MObject {
    let idx = index as usize;

    if index < 0 || idx > arr.elements.len() {
        NULL
    } else {
        if let Some(o) = arr.elements.get(idx) {
            o.clone()
        } else {
            NULL
        }
    }
}

fn eval_hash_literal_expression(h: HashLiteral, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    let mut pairs = HashMap::new();

    for (k_node, v_node) in h.pairs {
        let key = eval(MNode::Expr(k_node), env.clone())?;
        if let MObject::Err(_) = key { return Ok(key); };

        let hash_key = match key.clone() {
            MObject::Str(x) => HashKey::Str(x),
            MObject::Int(x) => HashKey::Int(x),
            MObject::Bool(x) => HashKey::Bool(x),
            _ => return Ok(new_error(format!("unusable as hash key: {}", key))),
        };

        let value = eval(MNode::Expr(v_node), env.clone())?;
        if let MObject::Err(_) = value { return Ok(value); };

        let hash_value = HashPair { key, value };

        pairs.insert(hash_key, hash_value);
    };

    Ok(
        MObject::Hash(
            MHash {
                pairs,
            }
        )
    )
}

fn quote(arg: Option<&Expr>, env: Rc<RefCell<Environment>>) -> Result<MObject> {
    let node = if let Some(expr) = arg {
        eval_unquote_calls(expr.clone(), env)
    } else {
        return Ok(new_error("argument required for quote, got: null".to_string()));
    };

    Ok(
        MObject::Quote(
            Quote {
                node,
            }
        )
    )
}

fn eval_unquote_calls(node: Expr, env: Rc<RefCell<Environment>>) -> MNode {
    // MNode::Expr(node)
    crate::ast::modify(MNode::Expr(node), env, |node: MNode, env: Rc<RefCell<Environment>>| -> MNode {
        if !is_unquote_call(&node) { return node; };

        let call = match node {
            MNode::Expr(Expr::Call(ref c)) => c,
            _ => return node,
        };

        if call.args.len() != 1 { return node; };

        if let Some(arg) = call.args.get(0) {
            match eval(MNode::Expr(arg.clone()), env) {
                Ok(obj) => convert_obj_to_ast_node(obj),
                _ => node,
            }
        } else {
            node
        }
    })
}

fn convert_obj_to_ast_node(obj: MObject) -> MNode {
    match obj {
        MObject::Int(x) => MNode::Expr(
            Expr::Int(
                IntegerLiteral {
                    token: Token { token_type: TokenType::INT, literal: format!("{}", x.value) },
                    value: x.value,
                }
            )
        ),
        MObject::Bool(x) => {
            let token = if x.value {
                Token { token_type: TokenType::TRUE, literal: "true".to_string() }
            } else {
                Token { token_type: TokenType::FALSE, literal: "false".to_string() }
            };
            MNode::Expr(
                Expr::Bool(
                    BooleanLiteral {
                        token,
                        value: x.value,
                    },
                ),
            )
        },
        MObject::Quote(q) => q.node,
        _ => MNode::Expr(
            Expr::Int(
                IntegerLiteral {
                    token: Token { token_type: TokenType::INT, literal: format!("{}", 0) },
                    value: 0,
                }
            )
        ),
    }
}

fn is_unquote_call(node: &MNode) -> bool {
    match node {
        MNode::Expr(Expr::Call(c)) => c.function.token_literal() == "unquote",
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexer::{lexer::Lexer, token::Token}, parser::parser::Parser};

    use std::io::Read;


    fn test_eval(input: String) -> Result<MObject> {
        let lex = Lexer::new(input.as_bytes().bytes().peekable())?;
        let mut parser = Parser::new(lex.peekable())?;
        let program = parser.parse()?;

        check_parser_errors(parser)?;
        let env = Environment::new();

        eval(MNode::Prog(program), env)
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
            "if (false) { 10 }".to_string(),
            "if (1 > 2) { 10 }".to_string(),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        }

        for tt in nil_tests {
            let evaluated = test_eval(tt)?;
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
            ("\"Hello\" - \"World\"".to_string(), "unknown operator: Hello - World".to_string()),
            ("len(1)".to_string(), "argument to 'len' not supported, got: 1".to_string()),
            ("len(\"one\", \"two\")".to_string(), "wrong number of arguments, got: 2, want: 1".to_string()),
            ("first(1)".to_string(), "argument to 'first' not supported, got: 1".to_string()),
            ("first(\"one\", \"two\")".to_string(), "wrong number of arguments, got: 2, want: 1".to_string()),
            ("last(1)".to_string(), "argument to 'last' not supported, got: 1".to_string()),
            ("last(\"one\", \"two\")".to_string(), "wrong number of arguments, got: 2, want: 1".to_string()),
            ("rest(1)".to_string(), "argument to 'rest' not supported, got: 1".to_string()),
            ("rest(\"one\", \"two\")".to_string(), "wrong number of arguments, got: 2, want: 1".to_string()),
            ("push(1, 2)".to_string(), "first argument to 'push' not supported, got: 1".to_string()),
            ("push(\"one\")".to_string(), "wrong number of arguments, got: 1, want: 2".to_string()),
            ("{ [2]: true }".to_string(), "unusable as hash key: [2]".to_string()),
            ("{ true: true }[[2]]".to_string(), "unusable as hash key: [2]".to_string()),
            ("quote()".to_string(), "argument required for quote, got: null".to_string()),
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

    #[test]
    fn test_self_ref_closures() -> Result<()> {
        let input = "
            let fibonacci = fn(x) {
                if (x == 0) {
                    0
                } else {
                    if (x == 1) {
                        return 1;
                    } else {
                        fibonacci(x - 1) + fibonacci(x - 2);
                    }
                }
            };
            fibonacci(6);
        ".to_string();

        test_integer_obj(8, test_eval(input)?)
    }

    #[test]
    fn test_string_literal() -> Result<()> {
        let input = "\"Hello World!\"".to_string();
        let evaluated = test_eval(input)?;

        if let MObject::Str(x) = evaluated {
            assert_eq!("Hello World!".to_string(), x.value);
        } else {
            panic!("Expected string literal, got: {}", evaluated);
        }

        Ok(())
    }

    #[test]
    fn test_string_concatenation() -> Result<()> {
        let input = "\"Hello\" + \" \" + \"World!\"".to_string();
        let evaluated = test_eval(input)?;

        if let MObject::Str(x) = evaluated {
            assert_eq!("Hello World!".to_string(), x.value);
        } else {
            panic!("Expected string literal, got: {}", evaluated);
        }

        Ok(())
    }

    #[test]
    fn test_builtin_functions() -> Result<()> {
        let tests = vec![
            ("len(\"\")".to_string(), 0),
            ("len(\"four\")".to_string(), 4),
            ("len(\"hello world\")".to_string(), 11),
            ("len([1, 2])".to_string(), 2),
            ("len([1])".to_string(), 1),
            ("len([])".to_string(), 0),
            ("first([1])".to_string(), 1),
            ("first([1, true])".to_string(), 1),
            ("last([1])".to_string(), 1),
            ("last([true, 1])".to_string(), 1),
        ];

        let nil_tests = vec![
            "first([])".to_string(),
            "last([])".to_string(),
        ];

        let bool_tests = vec![
            "first([true, 2, false])".to_string(),
            "last([false, 2, true])".to_string(),
        ];

        let str_tests = vec![
            ("rest([1, true, \"foobar\"])".to_string(), "[true, \"foobar\"]".to_string()),
            ("rest([1, true])".to_string(), "[true]".to_string()),
            ("rest([1])".to_string(), "[]".to_string()),
            ("rest([])".to_string(), "null".to_string()),
            ("push([1, true], 5)".to_string(), "[1, true, 5]".to_string()),
            ("push([1], 5)".to_string(), "[1, 5]".to_string()),
            ("push([], 5)".to_string(), "[5]".to_string()),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        };

        for tt in nil_tests {
            let evaluated = test_eval(tt)?;
            assert_eq!(NULL, evaluated);
        };

        for tt in bool_tests {
            let evaluated = test_eval(tt)?;
            test_boolean_obj(true, evaluated)?;
        };

        for tt in str_tests {
            let evaluated = test_eval(tt.0)?;
            assert_eq!(tt.1, format!("{}", evaluated));
        };

        Ok(())
    }

    #[test]
    fn test_array_literal() -> Result<()> {
        let input = "[1, 2 * 2, 3 + 3]".to_string();
        let evaluated = test_eval(input)?;

        if let MObject::Array(mut arr) = evaluated {
            assert_eq!(3, arr.elements.len());

            test_integer_obj(6, arr.elements.pop().unwrap())?;
            test_integer_obj(4, arr.elements.pop().unwrap())?;
            test_integer_obj(1, arr.elements.pop().unwrap())?;
        } else {
            panic!("Expected array literal, got: {}", evaluated);
        }

        Ok(())
    }

    #[test]
    fn test_index_expressions() -> Result<()> {
        let tests = vec![
            ("[1, 2, 3][0]".to_string(), 1),
            ("[1, 2, 3][1]".to_string(), 2),
            ("[1, 2, 3][2]".to_string(), 3),
            ("let i = 0; [1][i];".to_string(), 1),
            ("[1, 2, 3][1 + 1];".to_string(), 3),
            ("let myArray = [1, 2, 3]; myArray[2];".to_string(), 3),
            ("let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];".to_string(), 6),
            ("let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i]".to_string(), 2),
            ("{\"foo\": 5}[\"foo\"]".to_string(), 5),
            (r#"let key = "foo"; {"foo": 5}[key]"#.to_string(), 5),
            (r#"{5: 5}[5]"#.to_string(), 5),
            ("{true: 5}[true]".to_string(), 5),
            ("{false: 5}[false]".to_string(), 5),
        ];

        let nil_tests = vec![
            "[1, 2, 3][3]".to_string(),
            "[1, 2, 3][-1]".to_string(),
            r#"{"foo": 5}["bar"]"#.to_string(),
            r#"{}["foo"]"#.to_string(),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;
            test_integer_obj(tt.1, evaluated)?;
        }

        for tt in nil_tests {
            let evaluated = test_eval(tt)?;
            assert_eq!(NULL, evaluated);
        }

        Ok(())
    }

    #[test]
    fn test_hash_literal() -> Result<()> {
        let input = r###"
            let two = "two";
            {
                "one": 10 - 9,
                two: 1 + 1,
                "thr" + "ee": 6 / 2,
                4: 4,
                true: 5,
                false: 6
            }
            "###.to_string();
        let evaluated = test_eval(input)?;

        let str_key_tests = vec![
            (MString { value: "one".to_string() }, 1),
            (MString { value: "two".to_string() }, 2),
            (MString { value: "three".to_string() }, 3),
        ];

        let int_key_tests = vec![
            (4, 4),
        ];

        let bool_key_tests = vec![
            (true, 5),
            (false, 6),
        ];

        if let MObject::Hash(h) = evaluated {
            assert_eq!(6, h.pairs.len());

            for tt in str_key_tests {
                let key = HashKey::Str(tt.0.clone());
                let pair = h.pairs.get(&key).unwrap();

                assert_eq!(MObject::Str(tt.0), pair.key);
                test_integer_obj(tt.1, pair.value.clone())?;
            };

            for tt in int_key_tests {
                let key = HashKey::Int(Integer { value: tt.0.clone() });
                let pair = h.pairs.get(&key).unwrap();

                test_integer_obj(tt.0, pair.key.clone())?;
                test_integer_obj(tt.1, pair.value.clone())?;
            };

            for tt in bool_key_tests {
                let key = HashKey::Bool(Boolean { value: tt.0 });
                let pair = h.pairs.get(&key).unwrap();

                test_boolean_obj(tt.0, pair.key.clone())?;
                test_integer_obj(tt.1, pair.value.clone())?;
            };
        } else {
            panic!("Expected hash literal, got: {}", evaluated);
        }

        Ok(())
    }

    #[test]
    fn test_quote() -> Result<()> {
        let tests = vec![
            ("quote(5)".to_string(), "5".to_string()),
            ("quote(5 + 8)".to_string(), "(5 + 8)".to_string()),
            ("quote(foobar)".to_string(), "foobar".to_string()),
            ("quote(foobar + barfoo)".to_string(), "(foobar + barfoo)".to_string()),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;

            if let MObject::Quote(quote) = evaluated {
                assert_eq!(tt.1, format!("{}", quote.node));
            } else {
                panic!("expected quote object, got: {}", evaluated);
            };
        };

        Ok(())
    }

    #[test]
    fn test_unquote() -> Result<()> {
        let tests = vec![
            ("quote(5)".to_string(), "5".to_string()),
            ("quote(5 + 8)".to_string(), "(5 + 8)".to_string()),
            ("quote(foobar)".to_string(), "foobar".to_string()),
            ("quote(foobar + barfoo)".to_string(), "(foobar + barfoo)".to_string()),
            ("quote(unquote(4))".to_string(), "4".to_string()),
            ("quote(unquote(4 + 4))".to_string(), "8".to_string()),
            ("quote(8 + unquote(4 + 4))".to_string(), "(8 + 8)".to_string()),
            ("quote(unquote(4 + 4) + 8)".to_string(), "(8 + 8)".to_string()),
            ("let foobar = 8; quote(unquote(foobar) + 8)".to_string(), "(8 + 8)".to_string()),
            ("quote(unquote(true))".to_string(), "true".to_string()),
            ("quote(unquote(true == false))".to_string(), "false".to_string()),
            ("quote(unquote(quote(4 + 4)))".to_string(), "(4 + 4)".to_string()),
            ("let quotedInfixExpression = quote(4 + 4); quote(unquote(4 + 4) + unquote(quotedInfixExpression))".to_string(), "(8 + (4 + 4))".to_string()),
        ];

        for tt in tests {
            let evaluated = test_eval(tt.0)?;

            if let MObject::Quote(quote) = evaluated {
                assert_eq!(tt.1, format!("{}", quote.node));
            } else {
                panic!("expected quote object, got: {}", evaluated);
            };
        };

        Ok(())
    }

    #[test]
    fn test_define_macros() -> Result<()> {
        let input = r#"
            let number = 1;
            let function = fn(x, y) { x + y };
            let mymacro = macro(x, y) { x + y; };
        "#.to_string();

        let lex = Lexer::new(input.as_bytes().bytes().peekable())?;
        let mut parser = Parser::new(lex.peekable())?;
        let mut program = parser.parse()?;

        check_parser_errors(parser)?;
        let env = Environment::new();

        define_macros(&mut program, env.clone());

        assert_eq!(2, program.stmts.len());
        let env = env.borrow();

        assert!(env.get(&"number".to_string()).is_none());
        assert!(env.get(&"function".to_string()).is_none());
        assert!(env.get(&"mymacro".to_string()).is_some());
        let mymacro = if let Some(m) = env.get(&"mymacro".to_string()) {
            match m.as_ref() {
                MObject::Macro(x) => x.clone(),
                x => panic!("mymacro is {}", x),
            }
        } else {
            panic!("mymacro is undefined");
        };

        assert_eq!(2, mymacro.params.len());
        assert_eq!("x", mymacro.params.get(0).unwrap().value);
        assert_eq!("y", mymacro.params.get(1).unwrap().value);

        assert_eq!("(x + y)", format!("{}", mymacro.body));

        Ok(())
    }

    #[test]
    fn test_expand_macros() -> Result<()> {
        let tests = vec![
            (
                r#"
                let infixExpression = macro() { quote(1 + 2); };

                infixExpression();
                "#.to_string(),
                "(1 + 2)".to_string(),
            ),
            (
                r#"
                let reverse = macro(a, b) { quote(unquote(b) - unquote(a)); };

                reverse(2 + 2, 10 - 5);
                "#.to_string(),
                "((10 - 5) - (2 + 2))".to_string(),
            ),
            (
                r#"
                let unless = macro(condition, consequence, alternative) {
                    quote(if (!(unquote(condition))) {
                        unquote(consequence);
                    } else {
                        unquote(alternative);
                    });
                };

                unless(10 > 5, puts("not greater"), puts("greater"));
                "#.to_string(),
                r#"if (!(10 > 5)) { puts("not greater") } else { puts("greater") }"#.to_string(),
                ),
        ];

        for tt in tests {
            let lex = Lexer::new(tt.0.as_bytes().bytes().peekable())?;
            let mut parser = Parser::new(lex.peekable())?;
            let mut program = parser.parse()?;

            check_parser_errors(parser)?;
            let env = Environment::new();

            define_macros(&mut program, env.clone());
            let expanded = expand_macros(program, env);
            assert_eq!(tt.1, format!("{}", expanded));
        };

        Ok(())
    }
}

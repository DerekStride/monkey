use std::collections::HashMap;

use crate::{
    error::{Result, Error},
    compiler::code::*,
    object::*,
    compiler::compiler::Bytecode, builtin,
};

use byteorder::{ByteOrder, BigEndian};

const STACK_SIZE: usize = 2048;
const GLOBALS_SIZE: usize = 2usize.pow(16);
const MAX_FRAMES: usize = 1024;


#[derive(Debug)]
struct Frame {
    cl: Closure,
    ip: usize,
    bp: usize,
}

impl Frame {
    fn new(cl: Closure, bp: usize) -> Self {
        Self {
            cl,
            bp,
            ip: 0,
        }
    }

    fn instructions(&self) -> &Instructions {
        &self.cl.f.instructions
    }
}

#[derive(Debug)]
pub struct Vm {
    constants: Vec<MObject>,
    globals: Vec<MObject>,

    frames: Vec<Frame>,
    stack: Vec<MObject>,
    last_op_pop_element: Option<MObject>,
}

impl Vm {
    pub fn new(bytecode: Bytecode) -> Self {
        let mut frames = Vec::with_capacity(MAX_FRAMES);
        frames.push(Frame::new(
            Closure {
                f: CompiledFunction {
                    instructions: bytecode.instructions,
                    num_locals: 0,
                    num_params: 0,
                },
                free: Vec::new(),
            },
            0,
        ));
        Self {
            constants: bytecode.contstants,
            globals: Vec::with_capacity(GLOBALS_SIZE),

            frames,
            stack: Vec::with_capacity(STACK_SIZE),
            last_op_pop_element: None,
        }
    }

    pub fn with_state(bytecode: Bytecode, globals: Vec<MObject>) -> Self {
        let mut frames = Vec::with_capacity(MAX_FRAMES);
        frames.push(Frame::new(
            Closure {
                f: CompiledFunction {
                    instructions: bytecode.instructions,
                    num_locals: 0,
                    num_params: 0,
                },
                free: Vec::new(),
            },
            0,
        ));
        Self {
            constants: bytecode.contstants,
            globals,

            frames,
            stack: Vec::with_capacity(STACK_SIZE),
            last_op_pop_element: None,
        }
    }

    pub fn globals(&self) -> Vec<MObject> {
        self.globals.clone()
    }

    pub fn run(&mut self) -> Result<()> {
        while self.current_frame().ip < self.current_frame().instructions().len() {
            let frame = self.pop_frame();
            let mut ip = frame.ip;
            let mut bp = frame.bp;
            let mut cl = frame.cl;
            let instructions: &[u8] = &cl.f.instructions;
            let op = instructions[ip];
            ip += 1;

            match op {
                OP_CONSTANT => {
                    let const_idx: usize = BigEndian::read_u16(&instructions[ip..]).into();
                    ip += 2;

                    self.push(self.constants[const_idx].clone())?;
                },
                OP_CLOSURE => {
                    let const_idx: usize = BigEndian::read_u16(&instructions[ip..]).into();
                    let num_free: usize = instructions[ip + 2].into();
                    ip += 3;

                    let mut free = Vec::with_capacity(num_free);

                    for i in 0..num_free {
                        free.push(self.stack[self.stack.len() - num_free + i].clone());
                    };

                    let closure = match &self.constants[const_idx] {
                        MObject::CompiledFn(f) => {
                            MObject::Closure(
                                Closure {
                                    f: f.clone(),
                                    free,
                                },
                            )
                        },
                        x => return Err(Error::new(format!("Cannot turn {} into a closure.", x))),
                    };
                    self.push(closure)?;
                },
                OP_CURRENT_CLOSURE => {
                    self.push(MObject::Closure(cl.clone()))?;
                },
                OP_ADD..=OP_DIV => self.add_op(op)?,
                OP_TRUE => self.push(TRUE)?,
                OP_FALSE => self.push(FALSE)?,
                OP_EQUAL..=OP_GREATER_THAN => self.comparison_op(op)?,
                OP_MINUS => {
                    let object = self.pop()?;
                    match object {
                        MObject::Int(x) => self.push(MObject::Int(Integer { value: -x.value }))?,
                        _ => return Err(Error::new(format!("object not an integer: {}", object))),
                    };
                },
                OP_BANG => {
                    match self.pop()? {
                        MObject::Bool(x) => self.push(native_bool_to_boolean(!x.value))?,
                        NULL => self.push(TRUE)?,
                        _ => self.push(FALSE)?,
                    };
                },
                OP_INDEX => self.index_op()?,
                OP_JUMP_NOT_TRUE => {
                    if is_truthy(self.pop()?) {
                        ip += 2;
                    } else {
                        ip = BigEndian::read_u16(&instructions[ip..]).into();
                    };
                },
                OP_SET_GLOBAL => {
                    let globals_idx: usize = BigEndian::read_u16(&instructions[ip..]).into();
                    ip += 2;

                    let obj = self.pop()?;
                    self.globals.insert(globals_idx, obj);
                },
                OP_GET_GLOBAL => {
                    let globals_idx: usize = BigEndian::read_u16(&instructions[ip..]).into();
                    ip += 2;

                    let obj = match self.globals.get(globals_idx) {
                        Some(x) => (*x).clone(),
                        None => return Err(Error::new(format!("No global found for index: {}, len: {}", globals_idx, self.globals.len()))),
                    };
                    self.push(obj)?;
                },
                OP_SET_LOCAL => {
                    let locals_idx: u8 = instructions[ip];
                    ip += 1;

                    let mut obj = self.pop()?;
                    let idx = self.current_frame().bp + (locals_idx as usize);
                    let stack_null = match self.stack.get_mut(idx) {
                        Some(x) => x,
                        None => return Err(
                            Error::new(
                                format!(
                                    "No local on stack. index: {}, bp: {}, len: {}, stack:\n{:?}",
                                    locals_idx,
                                    self.current_frame().bp,
                                    self.stack.len(),
                                    self.stack,
                                )
                            )
                        ),
                    };
                    std::mem::swap(
                        stack_null,
                        &mut obj,
                    );
                },
                OP_GET_LOCAL => {
                    let locals_idx: u8 = instructions[ip];
                    ip += 1;

                    let idx = self.current_frame().bp + (locals_idx as usize);
                    let obj = match self.stack.get(idx) {
                        Some(x) => x.clone(),
                        None => return Err(
                            Error::new(
                                format!(
                                    "No local on stack. index: {}, bp: {}, len: {}, stack:\n{:?}",
                                    locals_idx,
                                    self.current_frame().bp,
                                    self.stack.len(),
                                    self.stack,
                                )
                            )
                        ),
                    };
                    self.stack.push(obj);
                },
                OP_GET_FREE => {
                    let free_idx: usize = instructions[ip].into();
                    ip += 1;

                    self.stack.push(cl.free[free_idx].clone());
                },
                OP_GET_BUILTIN => {
                    let builtin_idx = instructions[ip];
                    ip += 1;

                    let f = match builtin::get_builtin_by_index(builtin_idx) {
                        Some(x) => x,
                        None => return Err(Error::new(format!("No builtin defined with index={}", builtin_idx))),
                    };

                    self.push(f)?;
                },
                OP_ARRAY => {
                    let array_len: usize = BigEndian::read_u16(&instructions[ip..]).into();
                    ip += 2;

                    let mut elements = vec![];
                    for _ in 0..array_len {
                        elements.push(self.pop()?);
                    };
                    elements.reverse();

                    self.push(MObject::Array(MArray { elements }))?;
                },
                OP_HASH => {
                    let hash_len: usize = BigEndian::read_u16(&instructions[ip..]).into();
                    ip += 2;

                    let mut pairs = HashMap::new();
                    for _ in 0..hash_len {
                        let value = self.pop()?;
                        let key = self.pop()?;
                        let hash_key = match key.clone() {
                            MObject::Str(x) => HashKey::Str(x),
                            MObject::Int(x) => HashKey::Int(x),
                            MObject::Bool(x) => HashKey::Bool(x),
                            _ => panic!("Expected key to be Int, Str, or Bool. Got: {:?}", key),
                        };

                        let pair = HashPair { key, value };

                        pairs.insert(hash_key, pair);
                    };

                    self.push(MObject::Hash(MHash { pairs }))?;
                },
                OP_CALL => {
                    let num_args = instructions[ip]; 
                    ip += 1;

                    if let Some((closure, bp)) = self.execute_call(num_args)? {
                        self.push_frame(Frame { cl, ip, bp });
                        ip = 0;
                        cl = closure;
                    };
                },
                OP_RETURN_VAL => {
                    let retval = self.pop()?;
                    let frame = self.pop_frame();
                    ip = frame.ip;
                    bp = frame.bp;
                    cl = frame.cl;

                    // Pop off the local variables
                    for _ in bp..self.stack.len() { self.pop()?; };
                    self.push(retval)?;
                },
                OP_RETURN => {
                    let frame = self.pop_frame();
                    ip = frame.ip;
                    bp = frame.bp;
                    cl = frame.cl;

                    // Pop off the local variables
                    for _ in bp..self.stack.len() { self.pop()?; };
                    self.push(NULL)?;
                },
                OP_JUMP => ip = BigEndian::read_u16(&instructions[ip..]).into(),
                OP_NULL => self.push(NULL)?,
                OP_POP => self.last_op_pop_element = Some(self.pop()?),
                _ => {
                    let code = MCode::new();
                    let def = code.lookup(&op)?;
                    return Err(Error::new(format!("Opcode not implemented: {}", def.name)))
                },
            };

            self.push_frame(Frame { cl, ip, bp });
        }

        Ok(())
    }

    pub fn stack_top(&self) -> Option<&MObject> {
        self.last_op_pop_element.as_ref()
    }

    fn push(&mut self, o: MObject) -> Result<()> {
        if self.stack.len() < STACK_SIZE {
            self.stack.push(o);
            Ok(())
        } else {
            Err(Error::new("Stack overflow".to_string()))
        }
    }

    fn pop(&mut self) -> Result<MObject> {
        match self.stack.pop() {
            Some(x) => Ok(x),
            None => Err(Error::new("Stack is empty".to_string())),
        }
    }

    fn current_frame(&self) -> &Frame {
        self.frames.last().unwrap()
    }

    fn push_frame(&mut self, frame: Frame) {
        self.frames.push(frame)
    }

    fn pop_frame(&mut self) -> Frame {
        self.frames.pop().unwrap()
    }

    fn add_op(&mut self, op: u8) -> Result<()> {
        let right = self.pop()?;
        let left = self.pop()?;

        if let MObject::Int(left_val) = left {
            if let MObject::Int(right_val) = right {
                return self.arithmetic_op(left_val.value, op, right_val.value);
            }
        } else if let MObject::Str(ref left_val) = left {
            if let MObject::Str(ref right_val) = right {
                match op {
                    OP_ADD => {
                        let value = format!("{}{}", left_val.value, right_val.value);
                        return self.push(MObject::Str(MString { value }));
                    },
                    _ => {},
                }
            }
        };

        Err(Error::new(format!("type mismatch: {} {} {}", left, op, right)))
    }

    fn arithmetic_op(&mut self, left: i128, op: u8, right: i128) -> Result<()> {
        let value = match op {
            OP_ADD => left + right,
            OP_SUB => left - right,
            OP_MUL => left * right,
            OP_DIV => left / right,
            _ => unreachable!(),
        };
        self.push(MObject::Int(Integer { value }))
    }

    fn comparison_op(&mut self, op: u8) -> Result<()> {
        let right = self.pop()?;
        let left = self.pop()?;

        if let MObject::Int(left_val) = left {
            if let MObject::Int(right_val) = right {
                let value = match op {
                    OP_EQUAL => left_val == right_val,
                    OP_NOT_EQUAL => left_val != right_val,
                    OP_GREATER_THAN => left_val > right_val,
                    _ => unreachable!(),
                };
                return self.push(native_bool_to_boolean(value));
            }
        } else if let MObject::Bool(left_val) = left {
            if let MObject::Bool(right_val) = right {
                let value = match op {
                    OP_EQUAL => left_val == right_val,
                    OP_NOT_EQUAL => left_val != right_val,
                    _ => unreachable!(),
                };
                return self.push(native_bool_to_boolean(value));
            }
        };

        Err(Error::new(format!("type mismatch: {} {} {}", left, op, right)))
    }

    fn index_op(&mut self) -> Result<()> {
        let index = self.pop()?;
        let obj = self.pop()?;

        let value = match obj {
            MObject::Array(ref x) => {
                if let MObject::Int(ref i) = index {
                    match x.elements.get(i.value as usize) {
                        Some(v) => v.clone(),
                        None => NULL,
                    }
                } else {
                    return Err(Error::new(format!("OpIndex not implmented for: {}[{}]", obj, index)));
                }
            },
            MObject::Hash(ref h) => {
                let hash_key = match index {
                    MObject::Int(x) => HashKey::Int(x),
                    MObject::Str(x) => HashKey::Str(x),
                    MObject::Bool(x) => HashKey::Bool(x),
                    _ => return Err(Error::new(format!("Expected hash key to be Int, Str, or Bool. Got: {:?}", index))),
                };

                match h.pairs.get(&hash_key) {
                    Some(pair) => pair.value.clone(),
                    None => NULL,
                }
            }
            _ => return Err(Error::new(format!("OpIndex not implmented for: {}[{}]", obj, index))),
        };

        self.push(value)
    }

    fn execute_call(&mut self, num_args: u8) -> Result<Option<(Closure, usize)>> {
        let callee = self.pop()?;
        match callee {
            MObject::Closure(x) => self.call_function(x, num_args),
            MObject::Builtin(x) => self.call_builtin(x, num_args),
            _ => Err(Error::new(format!("Expected compiled funtion or builtin, got: {}", callee))),
        }
    }

    fn call_function(&mut self, callee: Closure, num_args: u8) -> Result<Option<(Closure, usize)>> {
        if callee.f.num_params != num_args {
            return Err(Error::new(format!("wrong number of arguments: want={}, got={}", callee.f.num_params, num_args)));
        };

        let num_locals = callee.f.num_locals;

        let bp = self.stack.len() - (num_args as usize);

        // Make room for the locals
        for _ in 0..num_locals { self.stack.push(NULL); };

        Ok(Some((callee, bp)))
    }

    fn call_builtin(&mut self, callee: builtin::Builtin, num_args: u8) -> Result<Option<(Closure, usize)>> {
        let mut args = Vec::new();
        for _ in 0..num_args { args.push(self.pop()?); };
        args.reverse();

        let result = match callee {
            builtin::Builtin::Len(len) => len(&mut args),
            builtin::Builtin::First(first) => first(&mut args),
            builtin::Builtin::Last(last) => last(&mut args),
            builtin::Builtin::Rest(rest) => rest(&mut args),
            builtin::Builtin::Push(push) => push(&mut args),
            builtin::Builtin::Puts(puts) => puts(&mut args),
        };

        self.push(result?)?;

        Ok(None)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    use std::io::Read;

    use crate::{
        ast::*,
        test_utils::*,
        compiler::compiler::Compiler,
        lexer::token::Token,
        parser::parser::Parser,
        lexer::lexer::Lexer,
    };

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

    fn parse(input: &[u8]) -> Result<Program> {
        let lexer = Lexer::new(input.bytes().peekable())?;
        let mut parser = Parser::new(lexer.peekable())?;
        let program = parser.parse()?;

        check_parser_errors(parser)?;

        Ok(program)
    }

    struct TestCase {
        input: String,
        expected: MObject,
    }

    fn run_vm_tests(tests: &[TestCase]) -> Result<()> {
        for tt in tests {
            let program = parse(tt.input.as_bytes())?;
            let mut compiler = Compiler::new();
            compiler.compile(MNode::Prog(program))?;

            let mut vm = Vm::new(compiler.bytecode());

            match vm.run() {
                Ok(_) => {},
                Err(e) => panic!("Error:\n{}\n\n{}\n", e, compiler),
            };

            let stack_top = match vm.stack_top() {
                Some(x) => x,
                None => panic!("No value on stack:\n{}\n", compiler),
            };

            assert_eq!(&tt.expected, stack_top, "\n\ninput:\n{}\n\n{}\n", tt.input, compiler);
        };

        Ok(())
    }

    #[test]
    fn test_integer_arithmetic() -> Result<()> {
        let tests = vec![
            TestCase { input: "1".to_string(), expected: i_to_o(1) },
            TestCase { input: "2".to_string(), expected: i_to_o(2) },
            TestCase { input: "1 + 2".to_string(), expected: i_to_o(3) },
            TestCase { input: "1 - 2".to_string(), expected: i_to_o(-1) },
            TestCase { input: "-1 - -2".to_string(), expected: i_to_o(1) },
            TestCase { input: "1 * 2".to_string(), expected: i_to_o(2) },
            TestCase { input: "4 / 2".to_string(), expected: i_to_o(2) },
            TestCase { input: "50 / 2 * 2 + 10 - 5".to_string(), expected: i_to_o(55) },
            TestCase { input: "5 + 5 + 5 + 5 - 10".to_string(), expected: i_to_o(10) },
            TestCase { input: "2 * 2 * 2 * 2 * 2".to_string(), expected: i_to_o(32) },
            TestCase { input: "5 * 2 + 10".to_string(), expected: i_to_o(20) },
            TestCase { input: "5 + 2 * 10".to_string(), expected: i_to_o(25) },
            TestCase { input: "5 * (2 + 10)".to_string(), expected: i_to_o(60) },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_boolean_expressions() -> Result<()> {
        let tests = vec![
            TestCase { input: "true".to_string(), expected: TRUE },
            TestCase { input: "!true".to_string(), expected: FALSE },
            TestCase { input: "!!true".to_string(), expected: TRUE },
            TestCase { input: "!5".to_string(), expected: FALSE },
            TestCase { input: "!!5".to_string(), expected: TRUE },
            TestCase { input: "false".to_string(), expected: FALSE },
            TestCase { input: "1 < 2".to_string(), expected: TRUE },
            TestCase { input: "1 > 2".to_string(), expected: FALSE },
            TestCase { input: "1 < 1".to_string(), expected: FALSE },
            TestCase { input: "1 > 1".to_string(), expected: FALSE },
            TestCase { input: "1 == 1".to_string(), expected: TRUE },
            TestCase { input: "1 != 1".to_string(), expected: FALSE },
            TestCase { input: "1 == 2".to_string(), expected: FALSE },
            TestCase { input: "1 != 2".to_string(), expected: TRUE },
            TestCase { input: "true == true".to_string(), expected: TRUE },
            TestCase { input: "false == false".to_string(), expected: TRUE },
            TestCase { input: "true == false".to_string(), expected: FALSE },
            TestCase { input: "true != false".to_string(), expected: TRUE },
            TestCase { input: "false != true".to_string(), expected: TRUE },
            TestCase { input: "(1 < 2) == true".to_string(), expected: TRUE },
            TestCase { input: "(1 < 2) == false".to_string(), expected: FALSE },
            TestCase { input: "(1 > 2) == true".to_string(), expected: FALSE },
            TestCase { input: "(1 > 2) == false".to_string(), expected: TRUE },
            TestCase { input: "!(if (false) { 5; })".to_string(), expected: TRUE },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_if_expressions() -> Result<()> {
        let tests = vec![
            TestCase { input: "if (true) { 10 }".to_string(), expected: i_to_o(10) },
            TestCase { input: "if (true) { 10 } else { 20 }".to_string(), expected: i_to_o(10) },
            TestCase { input: "if (false) { 10 } else { 20 } ".to_string(), expected: i_to_o(20) },
            TestCase { input: "if (1) { 10 }".to_string(), expected: i_to_o(10) },
            TestCase { input: "if (1 < 2) { 10 }".to_string(), expected: i_to_o(10) },
            TestCase { input: "if (1 < 2) { 10 } else { 20 }".to_string(), expected: i_to_o(10) },
            TestCase { input: "if (1 > 2) { 10 } else { 20 }".to_string(), expected: i_to_o(20) },
            TestCase { input: "if (false) { 10 }".to_string(), expected: NULL },
            TestCase { input: "if (1 > 2) { 10 }".to_string(), expected: NULL },
            TestCase { input: "if ((if (false) { 10 })) { 10 } else { 20 }".to_string(), expected: i_to_o(20) },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_let_statements() -> Result<()> {
        let tests = vec![
            TestCase { input: "let one = 1; one".to_string(), expected: i_to_o(1) },
            TestCase { input: "let one = 1; let two = 2; one + two".to_string(), expected: i_to_o(3) },
            TestCase { input: "let one = 1; let two = one + one; one + two".to_string(), expected: i_to_o(3) },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_string_expr() -> Result<()> {
        let tests = vec![
            TestCase { input: r#""monkey""#.to_string(), expected: s_to_o("monkey") },
            TestCase { input: r#""mon" + "key""#.to_string(), expected: s_to_o("monkey") },
            TestCase { input: r#""mon" + "key" + "banana""#.to_string(), expected: s_to_o("monkeybanana") },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_array_expr() -> Result<()> {
        let tests = vec![
            TestCase { input: "[]".to_string(), expected: MObject::Array(MArray { elements: vec![] }) },
            TestCase { input: r#"["mon", "key", "go!"]"#.to_string(), expected: MObject::Array(MArray { elements: vec![s_to_o("mon"), s_to_o("key"), s_to_o("go!")] }) },
            TestCase { input: "[1 + 2, 3 - 4, 5 * 6]".to_string(), expected: MObject::Array(MArray { elements: vec![i_to_o(1 + 2), i_to_o(3 - 4), i_to_o(5 * 6)] }) },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_hash_expr() -> Result<()> {
        let tests = vec![
            TestCase {
                input: "{}".to_string(),
                expected: mhash![],
            },
            TestCase {
                input: "{1: 2, 3: 4, 5: 6}".to_string(),
                expected: mhash![
                    (i_to_o(1), i_to_o(2)),
                    (i_to_o(3), i_to_o(4)),
                    (i_to_o(5), i_to_o(6)),
                ],
            },
            TestCase {
                input: "{1: 2 + 3, 4: 5 * 6}".to_string(),
                expected: mhash![
                    (i_to_o(1), i_to_o(2 + 3)),
                    (i_to_o(4), i_to_o(5 * 6)),
                ],
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_index_operation() -> Result<()> {
        let tests = vec![
            TestCase { input: "[1, 2, 3][1]".to_string(), expected: i_to_o(2) },
            TestCase { input: "[1, 2, 3][0 + 2]".to_string(), expected: i_to_o(3) },
            TestCase { input: "[[1, 1, 1]][0][0]".to_string(), expected: i_to_o(1) },
            TestCase { input: "[][0]".to_string(), expected: NULL },
            TestCase { input: "[1, 2, 3][99]".to_string(), expected: NULL },
            TestCase { input: "[1][-1]".to_string(), expected: NULL },
            TestCase { input: "{1: 1, 2: 2}[1]".to_string(), expected: i_to_o(1) },
            TestCase { input: "{1: 1, 2: 2}[2]".to_string(), expected: i_to_o(2) },
            TestCase { input: "{1: 1}[0]".to_string(), expected: NULL },
            TestCase { input: "{}[0]".to_string(), expected: NULL }
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_funtions_without_arguments() -> Result<()> {
        let tests = vec![
            TestCase {
                input: r#"
                    let fivePlusTen = fn() { 5 + 10; };
                    fivePlusTen();
                "#.to_string(),
                expected: i_to_o(15)
            },
            TestCase {
                input: r#"
                    let one = fn() { 1; };
                    let two = fn() { 2; };
                    one() + two()
                "#.to_string(),
                expected: i_to_o(3)
            },
            TestCase {
                input: r#"
                    let a = fn() { 1 };
                    let b = fn() { a() + 1 };
                    let c = fn() { b() + 1 };
                    c();
                "#.to_string(),
                expected: i_to_o(3)
            },
            TestCase {
                input: r#"
                    let earlyExit = fn() { return 99; 100; };
                    earlyExit();
                "#.to_string(),
                expected: i_to_o(99)
            },
            TestCase {
                input: r#"
                    let earlyExit = fn() { return 99; return 100; };
                    earlyExit();
                "#.to_string(),
                expected: i_to_o(99)
            },
            TestCase {
                input: r#"
                    let noReturn = fn() { };
                    noReturn();
                "#.to_string(),
                expected: NULL
            },
            TestCase {
                input: r#"
                    let noReturn = fn() { };
                    let noReturnTwo = fn() { noReturn(); };
                    noReturnTwo();
                    noReturn();
                "#.to_string(),
                expected: NULL
            },
            TestCase {
                input: r#"
                    let returnsOne = fn() { 1; };
                    let returnsOneReturner = fn() { returnsOne; };
                    returnsOneReturner()();
                "#.to_string(),
                expected: i_to_o(1)
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_funtions_with_bindings() -> Result<()> {
        let tests = vec![
            TestCase {
                input: r#"
                    let one = fn() { let one = 1; one };
                    one();
                "#.to_string(),
                expected: i_to_o(1)
            },
            TestCase {
                input: r#"
                    let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
                    oneAndTwo();
                "#.to_string(),
                expected: i_to_o(3)
            },
            TestCase {
                input: r#"
                    let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
                    let threeAndFour = fn() { let three = 3; let four = 4; three + four; };
                    oneAndTwo() + threeAndFour();
                "#.to_string(),
                expected: i_to_o(10)
            },
            TestCase {
                input: r#"
                    let firstFoobar = fn() { let foobar = 50; foobar; };
                    let secondFoobar = fn() { let foobar = 100; foobar; };
                    firstFoobar() + secondFoobar();
                "#.to_string(),
                expected: i_to_o(150)
            },
            TestCase {
                input: r#"
                    let globalSeed = 50;
                    let minusOne = fn() {
                        let num = 1;
                        globalSeed - num;
                    }
                    let minusTwo = fn() {
                        let num = 2;
                        globalSeed - num;
                    }
                    minusOne() + minusTwo();
                "#.to_string(),
                expected: i_to_o(97)
            },
            TestCase {
                input: r#"
                    let returnsOneReturner = fn() {
                        let returnsOne = fn() { 1; };
                        returnsOne;
                    };
                    returnsOneReturner()();
                "#.to_string(),
                expected: i_to_o(1)
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_funtions_with_arguments_and_bindings() -> Result<()> {
        let tests = vec![
            TestCase {
                input: r#"
                    let identity = fn(a) { a; };
                    identity(4);
                "#.to_string(),
                expected: i_to_o(4)
            },
            TestCase {
                input: r#"
                    let sum = fn(a, b) { a + b; };
                    sum(1, 2);
                "#.to_string(),
                expected: i_to_o(3)
            },
            TestCase {
                input: r#"
                    let sum = fn(a, b) {
                        let c = a + b;
                        c;
                    };
                    sum(1, 2);
                "#.to_string(),
                expected: i_to_o(3)
            },
            TestCase {
                input: r#"
                    let sum = fn(a, b) {
                        let c = a + b;
                        c;
                    };
                    sum(1, 2) + sum(3, 4);
                "#.to_string(),
                expected: i_to_o(10)
            },
            TestCase {
                input: r#"
                    let sum = fn(a, b) {
                        let c = a + b;
                        c;
                    };
                    let outer = fn() {
                        sum(1, 2) + sum(3, 4);
                    };
                    outer();
                "#.to_string(),
                expected: i_to_o(10)
            },
            TestCase {
                input: r#"
                    let globalNum = 10;

                    let sum = fn(a, b) {
                        let c = a + b;
                        c + globalNum;
                    };

                    let outer = fn() {
                        sum(1, 2) + sum(3, 4) + globalNum;
                    };

                    outer() + globalNum;
                "#.to_string(),
                expected: i_to_o(50)
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_functions_with_wrong_arguments() -> Result<()> {
        let tests = vec![
            (
                "fn() { 1; }(1);".to_string(),
                "wrong number of arguments: want=0, got=1".to_string(),
            ),
            (
                "fn(a) { a; }();".to_string(),
                "wrong number of arguments: want=1, got=0".to_string(),
            ),
            (
                "fn(a, b) { a + b; }(1);".to_string(),
                "wrong number of arguments: want=2, got=1".to_string(),
            ),
        ];

        for tt in tests {
            let program = parse(tt.0.as_bytes())?;
            let mut compiler = Compiler::new();
            compiler.compile(MNode::Prog(program))?;

            let mut vm = Vm::new(compiler.bytecode());

            match vm.run() {
                Ok(_) => panic!("Should have received error: Err({})", tt.1),
                Err(e) => assert_eq!(tt.1, e.to_string()),
            };
        };

        Ok(())
    }

    #[test]
    fn test_builtin_functions() -> Result<()> {
        let tests = vec![
            TestCase { input: r#"len("")"#.to_string(), expected: i_to_o(0) },
            TestCase { input: r#"len("four")"#.to_string(), expected: i_to_o(4) },
            TestCase { input: r#"len("hello world")"#.to_string(), expected: i_to_o(11) },
            TestCase { input: r#"len([1, 2, 3])"#.to_string(), expected: i_to_o(3) },
            TestCase { input: r#"len([])"#.to_string(), expected: i_to_o(0) },
            TestCase { input: r#"puts("hello", "world!")"#.to_string(), expected: NULL },
            TestCase { input: r#"first([1, 2, 3])"#.to_string(), expected: i_to_o(1) },
            TestCase { input: r#"first([])"#.to_string(), expected: NULL },
            TestCase { input: r#"last([1, 2, 3])"#.to_string(), expected: i_to_o(3) },
            TestCase { input: r#"last([])"#.to_string(), expected: NULL },
            TestCase { input: r#"rest([1, 2, 3])"#.to_string(), expected: mvec![i_to_o(2), i_to_o(3)] },
            TestCase { input: r#"rest([])"#.to_string(), expected: NULL },
            TestCase { input: r#"push([], 1)"#.to_string(), expected: mvec![i_to_o(1)] },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_builtins_with_wrong_arguments() -> Result<()> {
        let tests = vec![
            TestCase { input: "len(1)".to_string(), expected: merr!("argument to 'len' not supported, got: 1") },
            TestCase { input: r#"len("one", "two")"#.to_string(), expected: merr!("wrong number of arguments, got: 2, want: 1") },
            TestCase { input: "first(1)".to_string(), expected: merr!("argument to 'first' not supported, got: 1") },
            TestCase { input: "last(1)".to_string(), expected: merr!("argument to 'last' not supported, got: 1") },
            TestCase { input: "push(1, 1)".to_string(), expected: merr!("first argument to 'push' not supported, got: 1") },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_closures() -> Result<()> {
        let tests = vec![
            TestCase {
                input: r#"
                    let newClosure = fn(a) {
                        fn() { a; };
                    };
                    let closure = newClosure(99);
                    closure();
                "#.to_string(),
                expected: i_to_o(99),
            },
            TestCase {
                input: r#"
                    let newAdder = fn(a, b) {
                        fn(c) { a + b + c };
                    };
                    let adder = newAdder(1, 2);
                    adder(8);
                "#.to_string(),
                expected: i_to_o(11),
            },
            TestCase {
                input: r#"
                    let newAdder = fn(a, b) {
                        let c = a + b;
                        fn(d) { c + d };
                    };
                    let adder = newAdder(1, 2);
                    adder(8);
                "#.to_string(),
                expected: i_to_o(11),
            },
            TestCase {
                input: r#"
                    let newAdderOuter = fn(a, b) {
                        let c = a + b;
                        fn(d) {
                            let e = d + c;
                            fn(f) { e + f; };
                        };
                    };
                    let newAdderInner = newAdderOuter(1, 2)
                        let adder = newAdderInner(3);
                    adder(8);
                "#.to_string(),
                expected: i_to_o(14),
            },
            TestCase {
                input: r#"
                    let a = 1;
                    let newAdderOuter = fn(b) {
                        fn(c) {
                            fn(d) { a + b + c + d };
                        };
                    };
                    let newAdderInner = newAdderOuter(2)
                        let adder = newAdderInner(3);
                    adder(8);
                "#.to_string(),
                expected: i_to_o(14),
            },
            TestCase {
                input: r#"
                    let newClosure = fn(a, b) {
                        let one = fn() { a; };
                        let two = fn() { b; };
                        fn() { one() + two(); };
                    };
                    let closure = newClosure(9, 90);
                    closure();
                "#.to_string(),
                expected: i_to_o(99),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_recursive_functions() -> Result<()> {
        let tests = vec![
            TestCase {
                input: r#"
                    let countDown = fn(x) {
                        if (x == 0) {
                            return 0;
                        } else {
                            countDown(x - 1);
                        }
                    };
                    countDown(1);
                "#.to_string(),
                expected: i_to_o(0),
            },
            TestCase {
                input: r#"
                    let countDown = fn(x) {
                        if (x == 0) {
                            return 0;
                        } else {
                            countDown(x - 1);
                        }
                    };
                    let wrapper = fn() {
                        countDown(1);
                    };
                    wrapper();
                "#.to_string(),
                expected: i_to_o(0),
            },
            TestCase {
                input: r#"
                    let wrapper = fn() {
                        let countDown = fn(x) {
                            if (x == 0) {
                                return 0;
                            } else {
                                countDown(x - 1);
                            }
                        };
                        countDown(1);
                    };
                    wrapper();
                "#.to_string(),
                expected: i_to_o(0),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_recursive_fibonacci() -> Result<()> {
        let tests = vec![
            TestCase {
                input: r#"
                    let fibonacci = fn(x) {
                        if (x == 0) {
                            return 0;
                        } else {
                            if (x == 1) {
                                return 1;
                            } else {
                                fibonacci(x - 1) + fibonacci(x - 2);
                            }
                        }
                    };
                    fibonacci(15);
                "#.to_string(),
                expected: i_to_o(610),
            },
        ];

        run_vm_tests(&tests)
    }
}

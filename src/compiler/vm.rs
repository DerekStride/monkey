use crate::{
    error::{Result, Error},
    compiler::code::*,
    interpreter::object::*,
    compiler::compiler::Bytecode,
};

use byteorder::{ByteOrder, BigEndian};

const STACK_SIZE: usize = 2048;

pub struct Vm {
    instructions: Instructions,
    constants: Vec<MObject>,

    stack: Vec<MObject>,
    last_op_pop_element: Option<MObject>,
}

impl Vm {
    pub fn new(bytecode: Bytecode) -> Self {
        Self {
            instructions: bytecode.instructions,
            constants: bytecode.contstants,
            stack: Vec::with_capacity(STACK_SIZE),
            last_op_pop_element: None,
        }
    }

    pub fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.len() {
            let op = *self.instructions.get(ip).unwrap();
            ip += 1;

            match op {
                OP_CONSTANT => {
                    let const_idx: usize = BigEndian::read_u16(&self.instructions[ip as usize..]).into();
                    ip += 2;

                    self.push(self.constants[const_idx].clone())?;
                },
                OP_ADD..=OP_DIV => self.arithmetic_op(op)?,
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
                        _ => self.push(FALSE)?,
                    };
                },
                OP_JUMP_NOT_TRUE => {
                    if is_truthy(self.pop()?) {
                        ip += 2;
                    } else {
                        ip = BigEndian::read_u16(&self.instructions[ip..]).into();
                    };
                },
                OP_JUMP => ip = BigEndian::read_u16(&self.instructions[ip..]).into(),
                OP_NULL => self.push(NULL)?,
                OP_POP => self.last_op_pop_element = Some(self.pop()?),
                _ => {
                    let code = MCode::new();
                    let def = code.lookup(&op)?;
                    return Err(Error::new(format!("Opcode not implemented: {}", def.name)))
                },
            };
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

    fn arithmetic_op(&mut self, op: u8) -> Result<()> {
        let right = self.pop()?;
        let right_val = match right {
            MObject::Int(x) => x.value,
            _ => return Err(Error::new(format!("object not an integer: {}", right))),
        };

        let left = self.pop()?;
        let left_val = match left {
            MObject::Int(x) => x.value,
            _ => return Err(Error::new(format!("object not an integer: {}", left))),
        };

        let value = match op {
            OP_ADD => left_val + right_val,
            OP_SUB => left_val - right_val,
            OP_MUL => left_val * right_val,
            OP_DIV => left_val / right_val,
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

            let stack_top = vm.stack_top().unwrap();

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
        ];

        run_vm_tests(&tests)
    }
}

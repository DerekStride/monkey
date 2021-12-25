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
    mcode: MCode,
    sp: usize,
}

impl Vm {
    pub fn new(bytecode: Bytecode) -> Self {
        Self {
            instructions: bytecode.instructions,
            constants: bytecode.contstants,
            stack: Vec::with_capacity(STACK_SIZE),
            mcode: MCode::new(),
            sp: 0,
        }
    }

    pub fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.len() {
            let instruction = self.instructions.get(ip).unwrap();
            let def = self.mcode.lookup(instruction)?;
            let op = def.op;
            ip += 1;

            match op {
                OP_CONSTANT => {
                    let const_idx: usize = BigEndian::read_u16(&self.instructions[ip as usize..]).into();
                    ip += 2;

                    self.push(self.constants.get(const_idx).unwrap().clone())?;
                },
                OP_ADD => {
                    let right = self.pop()?;
                    let left = self.pop()?;

                    let right_val = match right {
                        MObject::Int(x) => x.value,
                        _ => return Err(Error::new(format!("cannot add object: {}", right))),
                    };
                    let left_val = match left {
                        MObject::Int(x) => x.value,
                        _ => return Err(Error::new(format!("cannot add object: {}", left))),
                    };

                    self.push(MObject::Int(Integer { value: left_val + right_val }))?;
                },
                _ => return Err(Error::new(format!("Invalid Opcode: {:x}", op))),
            };

        }

        Ok(())
    }

    pub fn stack_top(&self) -> Option<&MObject> {
        self.stack.last()
    }

    fn push(&mut self, o: MObject) -> Result<()> {
        if self.sp < STACK_SIZE {
            self.stack.push(o);
            self.sp += 1;
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

            vm.run()?;

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
        ];

        run_vm_tests(&tests)
    }
}

use core::fmt;

use crate::{
    interpreter::object::*,
    compiler::code::*,
    ast::*,
    error::Error,
};

type Result<T> = std::result::Result<T, Error>;

pub struct Bytecode {
    pub instructions: Instructions,
    pub contstants: Vec<MObject>,
}

pub struct Compiler  {
    instructions: Instructions,
    constants: Vec<MObject>,
    code: MCode,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            constants: Vec::new(),
            code: MCode::new(),
        }
    }

    pub fn compile(&mut self, node: MNode) -> Result<()> {
        match node {
            MNode::Prog(p) => {
                for stmt in p.stmts {
                    self.compile(MNode::Stmt(stmt))?
                };
            },
            MNode::Stmt(s) => {
                match s {
                    Stmt::Expression(stmt) => {
                        self.compile(MNode::Expr(stmt.expr))?;
                    },
                    _ => return Err(Error::new(format!("Compilation not implemented for: {}", s))),
                };
            },
            MNode::Expr(e) => {
                match e {
                    Expr::In(infix) => {
                        self.compile(MNode::Expr(*infix.left))?;
                        self.compile(MNode::Expr(*infix.right))?;
                        match infix.operator.as_str() {
                            "+" => self.emit(Opcode::OpAdd, vec![]),
                            _ => return Err(Error::new(format!("unknown operator: {}", infix.operator))),
                        };
                    },
                    Expr::Int(int) => {
                        let literal = Integer { value: int.value };
                        self.constants.push(MObject::Int(literal));
                        self.emit(Opcode::OpConstant, vec![(self.constants.len() - 1) as isize]);
                    },
                    _ => return Err(Error::new(format!("Compilation not implemented for: {}", e))),
                };
            },
        };

        Ok(())
    }

    fn emit(&mut self, op: Opcode, operands: Operand) {
        let mut ins = self.code.make(&op, &operands);
        self.instructions.append(&mut ins);
    }

    pub fn bytecode(&self) -> Bytecode {
        Bytecode {
            instructions: self.instructions.clone(),
            contstants: self.constants.clone(),
        }
    }
}

impl fmt::Display for Compiler {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Compiler {{\n\tinstructions:\n\t\t{}\n\tconstants:\n\t\t{}\n}}",
            self.code.format(&self.instructions)
                .lines()
                .map(|l| l.to_string())
                .collect::<Vec<String>>()
                .join("\n\t\t"),
            self.constants
                .iter()
                .enumerate()
                .map(|(i, o)| format!("{}: {}", i, o))
                .collect::<Vec<String>>()
                .join("\n\t\t")
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;
    use crate::{ast::Program, lexer::{lexer::Lexer, token::Token}, parser::parser::Parser, interpreter::object::Integer, compiler::code::{Opcode, MCode}};

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

    fn parse(input: String) -> Result<Program> {
        let lexer = Lexer::new(input.as_bytes().bytes().peekable())?;
        let mut parser = Parser::new(lexer.peekable())?;
        let program = parser.parse()?;

        check_parser_errors(parser)?;

        Ok(program)
    }

    fn test_instructions(expected_instructions: Vec<Instructions>, actual: Instructions) {
        let expected: Instructions = expected_instructions
            .into_iter()
            .flatten()
            .collect::<Instructions>();

        let mcode = MCode::new();
        assert_eq!(expected, actual, "\n\nwant:\n{}\ngot:\n{}\n", mcode.format(&expected), mcode.format(&actual));
    }

    fn test_constants(expected: Vec<MObject>, actual: Vec<MObject>) {
        assert_eq!(expected, actual);
    }

    struct TestCase {
        input: String,
        expected_instructions: Vec<Instructions>,
        expected_constants: Vec<MObject>,
    }

    fn run_compiler_tests(tests: Vec<TestCase>) -> Result<()> {
        for tt in tests {
            let program = parse(tt.input)?;
            let mut compiler = Compiler::new();
            compiler.compile(MNode::Prog(program))?;

            let bytecode = compiler.bytecode();

            test_instructions(tt.expected_instructions, bytecode.instructions);
            test_constants(tt.expected_constants, bytecode.contstants);
        };

        Ok(())
    }

    fn i_to_o(i: i128) -> MObject {
        MObject::Int(
            Integer {
                value: i,
            }
        )
    }

    #[test]
    fn test_integer_arithmetic() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: "1 + 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&Opcode::OpConstant, &vec![0]),
                    code.make(&Opcode::OpConstant, &vec![1]),
                    code.make(&Opcode::OpAdd, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }
}

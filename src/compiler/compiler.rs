use core::fmt;

use crate::{
    interpreter::object::*,
    compiler::code::*,
    ast::*,
    error::{Result, Error},
};

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
                        self.emit(OP_POP, vec![]);
                    },
                    _ => return Err(Error::new(format!("Compilation not implemented for: {}", s))),
                };
            },
            MNode::Expr(e) => {
                match e {
                    Expr::In(infix) => {
                        if infix.operator.as_str() == "<" {
                            self.compile(MNode::Expr(*infix.right))?;
                            self.compile(MNode::Expr(*infix.left))?;
                            self.emit(OP_GREATER_THAN, vec![]);
                            return Ok(());
                        }
                        self.compile(MNode::Expr(*infix.left))?;
                        self.compile(MNode::Expr(*infix.right))?;
                        match infix.operator.as_str() {
                            "+" => self.emit(OP_ADD, vec![]),
                            "-" => self.emit(OP_SUB, vec![]),
                            "*" => self.emit(OP_MUL, vec![]),
                            "/" => self.emit(OP_DIV, vec![]),
                            "==" => self.emit(OP_EQUAL, vec![]),
                            "!=" => self.emit(OP_NOT_EQUAL, vec![]),
                            ">" => self.emit(OP_GREATER_THAN, vec![]),
                            _ => return Err(Error::new(format!("unknown operator: {}", infix.operator))),
                        };
                    },
                    Expr::Pre(prefix) => {
                        self.compile(MNode::Expr(*prefix.right))?;

                        match prefix.operator.as_str() {
                            "!" => self.emit(OP_BANG, vec![]),
                            "-" => self.emit(OP_MINUS, vec![]),
                            _ => return Err(Error::new(format!("unknown operator: {}", prefix.operator))),
                        };
                    },
                    Expr::Int(int) => {
                        let literal = Integer { value: int.value };
                        self.constants.push(MObject::Int(literal));
                        self.emit(OP_CONSTANT, vec![(self.constants.len() - 1) as isize]);
                    },
                    Expr::Bool(x) => {
                        if x.value {
                            self.emit(OP_TRUE, vec![]);
                        } else {
                            self.emit(OP_FALSE, vec![]);
                        }
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

    use crate::{
        test_utils::*,
        compiler::code::MCode,
    };

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

    #[test]
    fn test_integer_arithmetic() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: "1 + 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_ADD, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 - 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_SUB, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 * 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_MUL, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 / 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_DIV, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "-1 - -2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_MINUS, &vec![]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_MINUS, &vec![]),
                    code.make(&OP_SUB, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_boolean_expressions() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: "true".to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_TRUE, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "false".to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_FALSE, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "!false".to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_FALSE, &vec![]),
                    code.make(&OP_BANG, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 < 2".to_string(),
                expected_constants: vec![2, 1].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_GREATER_THAN, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 > 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_GREATER_THAN, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 == 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_EQUAL, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "1 != 2".to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_NOT_EQUAL, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "true == false".to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_TRUE, &vec![]),
                    code.make(&OP_FALSE, &vec![]),
                    code.make(&OP_EQUAL, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "true != false".to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_TRUE, &vec![]),
                    code.make(&OP_FALSE, &vec![]),
                    code.make(&OP_NOT_EQUAL, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }
}

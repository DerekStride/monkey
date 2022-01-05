use std::fmt;

use crate::{
    object::*,
    compiler::{
        code::*,
        symbol_table::{SymbolTable, Scope},
    },
    ast::*,
    error::{Result, Error},
};

#[derive(Clone)]
pub struct Bytecode {
    pub instructions: Instructions,
    pub contstants: Vec<MObject>,
}

#[derive(Debug)]
struct EmittedInstruction {
    opcode: Opcode,
    position: usize,
}

impl fmt::Display for EmittedInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let code = MCode::new();
        let def = code.lookup(&self.opcode).unwrap();

        write!(
            f,
            "{:0>4} {}",
            self.position,
            def.name,
        )
    }
}

struct CompilationScope {
    instructions: Instructions,

    last_emitted_instruction: Option<EmittedInstruction>,
    prev_emitted_instruction: Option<EmittedInstruction>,
}

impl CompilationScope {
    fn new() -> Self {
        Self {
            instructions: Vec::new(),

            last_emitted_instruction: None,
            prev_emitted_instruction: None,
        }
    }

    fn emit(&mut self, code: &MCode, opcode: Opcode, operands: Operand) {
        let mut ins = code.make(&opcode, &operands);
        self.set_last_instruction(opcode, self.instructions.len());
        self.instructions.append(&mut ins);
    }

    fn set_last_instruction(&mut self, opcode: Opcode, position: usize) {
        std::mem::swap(&mut self.prev_emitted_instruction, &mut self.last_emitted_instruction);
        self.last_emitted_instruction = Some(EmittedInstruction { opcode, position });
    }

    fn last_instruction_is(&self, opcode: Opcode) -> bool {
        if let Some(x) = &self.last_emitted_instruction { return opcode == x.opcode; };
        false
    }

    fn remove_last_pop(&mut self) {
        self.instructions.pop();
        std::mem::swap(&mut self.last_emitted_instruction, &mut self.prev_emitted_instruction);
        self.prev_emitted_instruction = None;
    }

    fn replace_last_pop_with_return(&mut self, code: &MCode) {
        let emitted = self.last_emitted_instruction.as_mut().unwrap();
        emitted.opcode = OP_RETURN_VAL;

        let pos = emitted.position;
        let ins = code.make(&OP_RETURN_VAL, &vec![]);

        self.replace_instruction(pos, &ins);
    }

    fn replace_instruction(&mut self, pos: usize, ins: &[u8]) {
        for (i, &byte) in ins.iter().enumerate() {
            self.instructions[pos + i] = byte;
        };
    }

    fn change_operand(&mut self, code: &MCode, pos: usize, operand: &Operand) {
        let ins = code.make(&self.instructions[pos], operand);
        self.replace_instruction(pos, &ins);
    }
}

pub struct Compiler  {
    constants: Vec<MObject>,
    symbols: SymbolTable,
    scopes: Vec<CompilationScope>,

    code: MCode,
}

impl Compiler {
    #[cfg(test)]
    pub fn new() -> Self {
        let mut symbols = SymbolTable::new();

        symbols.define_builtin("len".to_string());
        symbols.define_builtin("first".to_string());
        symbols.define_builtin("last".to_string());
        symbols.define_builtin("rest".to_string());
        symbols.define_builtin("push".to_string());
        symbols.define_builtin("puts".to_string());

        Self {
            constants: Vec::new(),
            symbols,
            scopes: vec![CompilationScope::new()],
            code: MCode::new(),
        }
    }

    pub fn with_state(symbols: SymbolTable, constants: Vec<MObject>) -> Self {
        Self {
            constants,
            symbols,
            scopes: vec![CompilationScope::new()],
            code: MCode::new(),
        }
    }

    pub fn symbol_table(&self) -> SymbolTable {
        self.symbols.clone()
    }

    pub fn bytecode(&self) -> Bytecode {
        let instructions = self
            .current_scope()
            .instructions
            .clone();

        Bytecode {
            instructions,
            contstants: self.constants.clone(),
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
                    Stmt::Block(blk) => {
                        for stmt in blk.stmts {
                            self.compile(MNode::Stmt(stmt))?;
                        };
                    },
                    Stmt::Let(let_stmt) => {
                        self.compile(MNode::Expr(let_stmt.value))?;
                        let symbol = self.symbols.define(let_stmt.name.value);
                        let index = symbol.index;

                        let opcode = if symbol.scope == Scope::Global {
                            OP_SET_GLOBAL
                        } else {
                            OP_SET_LOCAL
                        };
                        self.emit(opcode, vec![index as isize]);
                    },
                    Stmt::Return(ret_stmt) => {
                        self.compile(MNode::Expr(ret_stmt.retval))?;
                        self.emit(OP_RETURN_VAL, vec![]);
                    },
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
                    Expr::Index(op) => {
                        self.compile(MNode::Expr(*op.left))?;
                        self.compile(MNode::Expr(*op.index))?;
                        self.emit(OP_INDEX, vec![]);
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
                    Expr::Str(x) => {
                        let literal = MString { value: x.value };
                        self.constants.push(MObject::Str(literal));
                        self.emit(OP_CONSTANT, vec![(self.constants.len() - 1) as isize]);
                    },
                    Expr::If(if_expr) => {
                        self.compile(MNode::Expr(*if_expr.condition))?;

                        // Emit a JumpNotTrue Opcode with a placeholder offset to rewrite later.
                        let jump_not_true_loc = self.current_instructions().len();
                        self.emit(OP_JUMP_NOT_TRUE, vec![0]);

                        self.compile(MNode::Stmt(Stmt::Block(if_expr.consequence)))?;
                        if self.last_instruction_is(OP_POP) { self.remove_last_pop() };

                        // Emit a Jump Opcode with a placeholder offset to rewrite later.
                        let jump_loc = self.current_instructions().len();
                        self.emit(OP_JUMP, vec![0]);

                        // Rewrite the JumpNotTrue offset placeholder.
                        let after_conseqence_loc = self.current_instructions().len();
                        self.change_operand(jump_not_true_loc, &vec![after_conseqence_loc as isize]);

                        if let Some(alternative) = if_expr.alternative {
                            self.compile(MNode::Stmt(Stmt::Block(alternative)))?;
                            if self.last_instruction_is(OP_POP) { self.remove_last_pop() };
                        } else {
                            self.emit(OP_NULL, vec![]);
                        };

                        // Rewrite the Jump offset placeholder.
                        let after_alternative_loc = self.current_instructions().len();
                        self.change_operand(jump_loc, &vec![after_alternative_loc as isize]);
                    },
                    Expr::Ident(ident) => {
                        let symbol = match self.symbols.resolve(&ident.value) {
                            Some(x) => x,
                            None => return Err(Error::new(format!("Identifier not found: {}", ident))),
                        };
                        let index = symbol.index;

                        let opcode = match symbol.scope {
                            Scope::Global => OP_GET_GLOBAL,
                            Scope::Local => OP_GET_LOCAL,
                            Scope::Builtin => OP_GET_BUILTIN,
                        };

                        self.emit(opcode, vec![index as isize]);
                    },
                    Expr::Array(array) => {
                        let len = array.elements.len() as isize;

                        for elem in array.elements {
                            self.compile(MNode::Expr(elem))?;
                        };
                        self.emit(OP_ARRAY, vec![len]);
                    },
                    Expr::Hash(hash) => {
                        let len = hash.pairs.len() as isize;
                        let mut sorted = hash
                            .pairs
                            .into_iter()
                            .collect::<Vec<(Expr, Expr)>>();
                        sorted.sort_by_cached_key(|(k, _)| k.to_string());

                        for (key, value) in sorted {
                            self.compile(MNode::Expr(key))?;
                            self.compile(MNode::Expr(value))?;
                        };
                        self.emit(OP_HASH, vec![len]);
                    },
                    Expr::Fn(function) => {
                        self.enter_scope(CompilationScope::new());

                        let num_params = function.params.len() as u8;
                        for param in function.params {
                            self.symbols.define(param.value);
                        };

                        self.compile(MNode::Stmt(Stmt::Block(function.body)))?;

                        if self.last_instruction_is(OP_POP) { self.replace_last_pop_with_return(); };
                        if !self.last_instruction_is(OP_RETURN_VAL) { self.emit(OP_RETURN, vec![]); };

                        let num_locals = self.symbols.len();
                        let scope = self.leave_scope();
                        let compiled_fn = CompiledFunction { num_locals, num_params, instructions: scope.instructions };

                        self.constants.push(MObject::CompiledFn(compiled_fn));
                        self.emit(OP_CLOSURE, vec![(self.constants.len() - 1) as isize, 0]);
                    },
                    Expr::Call(fn_call) => {
                        let len = fn_call.args.len() as isize;
                        for arg in fn_call.args {
                            self.compile(MNode::Expr(arg))?;
                        };

                        self.compile(MNode::Expr(*fn_call.function))?;

                        self.emit(OP_CALL, vec![len]);
                    },
                    _ => return Err(Error::new(format!("Compilation not implemented for expression: {}", e))),
                };
            },
        };

        Ok(())
    }

    fn emit(&mut self, op: Opcode, operands: Operand) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.emit(&self.code, op, operands);
        };
    }

    fn last_instruction_is(&self, opcode: Opcode) -> bool {
        self.scopes.last().unwrap().last_instruction_is(opcode)
    }

    fn remove_last_pop(&mut self) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.remove_last_pop();
        };
    }

    fn replace_last_pop_with_return(&mut self) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.replace_last_pop_with_return(&self.code);
        };
    }

    fn change_operand(&mut self, pos: usize, operand: &Operand) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.change_operand(&self.code, pos, operand);
        };
    }

    fn enter_scope(&mut self, scope: CompilationScope) {
        self.symbols = SymbolTable::enclose(self.symbols.clone());
        self.scopes.push(scope);
    }

    fn leave_scope(&mut self) -> CompilationScope {
        self.symbols = self.symbols.outer().unwrap();
        self.scopes.pop().unwrap()
    }

    fn current_scope(&self) -> &CompilationScope {
        self.scopes.last().unwrap()
    }

    fn current_instructions(&self) -> &[u8] {
        &self.current_scope().instructions
    }
}

impl fmt::Display for Compiler {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let scope = self.current_scope();
        write!(
            f,
            "Compiler {{\n\tinstructions:\n\t\t{}\n\tconstants:\n\t\t{}\n\tprev_instruction:\n\t\t{}\n\tlast_instruction:\n\t\t{}\n}}",
            self.code.format(self.current_instructions())
                .lines()
                .map(|l| l.to_string())
                .collect::<Vec<String>>()
                .join("\n\t\t"),
            self.constants
                .iter()
                .enumerate()
                .map(|(i, o)| format!("{}: {}", i, o))
                .collect::<Vec<String>>()
                .join("\n\t\t"),
            if let Some(x) = &scope.prev_emitted_instruction { format!("{}", x) } else { "None".to_string() },
            if let Some(x) = &scope.last_emitted_instruction { format!("{}", x) } else { "None".to_string() },
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
        assert_eq!(expected, actual, "\n\nInstructions:\nwant:\n{}\ngot:\n{}\n", mcode.format(&expected), mcode.format(&actual));
    }

    fn test_constants(expected: Vec<MObject>, actual: Vec<MObject>) {
        assert_eq!(
            expected,
            actual,
            "\n\nConstants:\nwant:\n{}\ngot:\n{}\n",
            expected
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>()
                .join("\n"),
            actual
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>()
                .join("\n"),
        );
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

    #[test]
    fn test_conditionals() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: "if (true) { 10 }; 3333;".to_string(),
                expected_constants: vec![10, 3333].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    // 0000
                    code.make(&OP_TRUE, &vec![]),
                    // 0001
                    code.make(&OP_JUMP_NOT_TRUE, &vec![10]),
                    // 0004
                    code.make(&OP_CONSTANT, &vec![0]),
                    // 0007
                    code.make(&OP_JUMP, &vec![11]),
                    // 0010
                    code.make(&OP_NULL, &vec![]),
                    // 0011
                    code.make(&OP_POP, &vec![]),
                    // 0012
                    code.make(&OP_CONSTANT, &vec![1]),
                    // 0015
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: "if (true) { 10 } else { 20 }; 3333;".to_string(),
                expected_constants: vec![10, 20, 3333].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    // 0000
                    code.make(&OP_TRUE, &vec![]),
                    // 0001
                    code.make(&OP_JUMP_NOT_TRUE, &vec![10]),
                    // 0004
                    code.make(&OP_CONSTANT, &vec![0]),
                    // 0007
                    code.make(&OP_JUMP, &vec![13]),
                    // 0010
                    code.make(&OP_CONSTANT, &vec![1]),
                    // 0013
                    code.make(&OP_POP, &vec![]),
                    // 0014
                    code.make(&OP_CONSTANT, &vec![2]),
                    // 0017
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_let_statements() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    let one = 1;
                    let two = 2;
                "#.to_string(),
                expected_constants: vec![1, 2].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    // 0000
                    code.make(&OP_CONSTANT, &vec![0]),
                    // 0003
                    code.make(&OP_SET_GLOBAL, &vec![0]),
                    // 0006
                    code.make(&OP_CONSTANT, &vec![1]),
                    // 0009
                    code.make(&OP_SET_GLOBAL, &vec![1]),
                ],
            },
            TestCase {
                input: "let one = 1; one;".to_string(),
                expected_constants: vec![1].iter().map(|i| i_to_o(*i) ).collect(),
                expected_instructions: vec![
                    // 0000
                    code.make(&OP_CONSTANT, &vec![0]),
                    // 0003
                    code.make(&OP_SET_GLOBAL, &vec![0]),
                    // 0006
                    code.make(&OP_GET_GLOBAL, &vec![0]),
                    // 0009
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_string_expressions() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    "monkey"
                "#.to_string(),
                expected_constants: vec!["monkey"].iter().map(|&x| s_to_o(x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    "mon" + "key"
                "#.to_string(),
                expected_constants: vec!["mon", "key"].iter().map(|&x| s_to_o(x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_ADD, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_array_expressions() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    []
                "#.to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_ARRAY, &vec![0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    ["mon", "key", "go!"]
                "#.to_string(),
                expected_constants: vec!["mon", "key", "go!"].iter().map(|&x| s_to_o(x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_ARRAY, &vec![3]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    [1 + 2, 3 - 4, 5 * 6]
                "#.to_string(),
                expected_constants: vec![1, 2, 3, 4, 5, 6].iter().map(|x| i_to_o(*x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_ADD, &vec![]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_CONSTANT, &vec![3]),
                    code.make(&OP_SUB, &vec![]),
                    code.make(&OP_CONSTANT, &vec![4]),
                    code.make(&OP_CONSTANT, &vec![5]),
                    code.make(&OP_MUL, &vec![]),
                    code.make(&OP_ARRAY, &vec![3]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_hash_expressions() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    {}
                "#.to_string(),
                expected_constants: vec![],
                expected_instructions: vec![
                    code.make(&OP_HASH, &vec![0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    {1: 2, 3: 4, 5: 6}
                "#.to_string(),
                expected_constants: vec![1, 2, 3, 4, 5, 6].iter().map(|x| i_to_o(*x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_CONSTANT, &vec![3]),
                    code.make(&OP_CONSTANT, &vec![4]),
                    code.make(&OP_CONSTANT, &vec![5]),
                    code.make(&OP_HASH, &vec![3]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    {1: 2 + 3, 4: 5 * 6}
                "#.to_string(),
                expected_constants: vec![1, 2, 3, 4, 5, 6].iter().map(|x| i_to_o(*x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_ADD, &vec![]),
                    code.make(&OP_CONSTANT, &vec![3]),
                    code.make(&OP_CONSTANT, &vec![4]),
                    code.make(&OP_CONSTANT, &vec![5]),
                    code.make(&OP_MUL, &vec![]),
                    code.make(&OP_HASH, &vec![2]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_index_operator() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    [1, 2, 3][1 + 1]
                "#.to_string(),
                expected_constants: vec![1, 2, 3, 1, 1].iter().map(|x| i_to_o(*x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_ARRAY, &vec![3]),
                    code.make(&OP_CONSTANT, &vec![3]),
                    code.make(&OP_CONSTANT, &vec![4]),
                    code.make(&OP_ADD, &vec![]),
                    code.make(&OP_INDEX, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    {1: 2}[2 - 1]
                "#.to_string(),
                expected_constants: vec![1, 2, 2, 1].iter().map(|x| i_to_o(*x) ).collect(),
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_HASH, &vec![1]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_CONSTANT, &vec![3]),
                    code.make(&OP_SUB, &vec![]),
                    code.make(&OP_INDEX, &vec![]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_functions() -> Result<()> {
        let code = MCode::new();
        let constants: Vec<MObject> = vec![5, 10]
            .iter()
            .map(|x| i_to_o(*x) )
            .collect();
        let func1 = MObject::CompiledFn(
            CompiledFunction {
                num_locals: 0,
                num_params: 0,
                instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_ADD, &vec![]),
                    code.make(&OP_RETURN_VAL, &vec![]),
                ].into_iter().flatten().collect(),
            }
        );
        let func2 = MObject::CompiledFn(
            CompiledFunction {
                num_locals: 0,
                num_params: 0,
                instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_POP, &vec![]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_RETURN_VAL, &vec![]),
                ].into_iter().flatten().collect(),
            }
        );
        let mut constants1 = constants.clone();
        let mut constants2 = constants.clone();

        constants1.push(func1);
        constants2.push(func2);

        let tests = vec![
            TestCase {
                input: r#"
                    fn() { return 5 + 10 }
                "#.to_string(),
                expected_constants: constants1.clone(),
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![2, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    fn() { 5 + 10 }
                "#.to_string(),
                expected_constants: constants1.clone(),
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![2, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    fn() { 5; 10 }
                "#.to_string(),
                expected_constants: constants2.clone(),
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![2, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_functions_without_return_values() -> Result<()> {
        let code = MCode::new();
        let func1 = MObject::CompiledFn(
            CompiledFunction {
                num_locals: 0,
                num_params: 0,
                instructions: vec![
                    code.make(&OP_RETURN, &vec![]),
                ].into_iter().flatten().collect(),
            }
        );

        let constants = vec![func1];

        let tests = vec![
            TestCase {
                input: r#"
                    fn() { }
                "#.to_string(),
                expected_constants: constants,
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![0, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_compiler_scopes() {
        let mut compiler = Compiler::new();
        assert_eq!(1, compiler.scopes.len());

        let global_symbol_table = compiler.symbol_table();
        compiler.emit(OP_MUL, vec![]);

        compiler.enter_scope(CompilationScope::new());
        assert_eq!(2, compiler.scopes.len());

        compiler.emit(OP_SUB, vec![]);

        let last = compiler.scopes.last().unwrap().last_emitted_instruction.as_ref().unwrap();

        assert_eq!(OP_SUB, last.opcode);
        assert_ne!(compiler.symbol_table(), global_symbol_table);

        compiler.leave_scope();
        assert_eq!(1, compiler.scopes.len());
        assert_eq!(compiler.symbol_table(), global_symbol_table);

        compiler.emit(OP_ADD, vec![]);
        let last = compiler.scopes.last().unwrap().last_emitted_instruction.as_ref().unwrap();
        let prev = compiler.scopes.last().unwrap().prev_emitted_instruction.as_ref().unwrap();

        assert_eq!(OP_ADD, last.opcode);
        assert_eq!(OP_MUL, prev.opcode);
    }

    #[test]
    fn test_function_calls() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    fn() { 24 }();
                "#.to_string(),
                expected_constants: vec![
                    i_to_o(24),
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 0,
                            num_params: 0,
                            instructions: vec![
                                code.make(&OP_CONSTANT, &vec![0]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    )
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![1, 0]),
                    code.make(&OP_CALL, &vec![0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    let noArg = fn() { 24 };
                    noArg();
                "#.to_string(),
                expected_constants: vec![
                    i_to_o(24),
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 0,
                            num_params: 0,
                            instructions: vec![
                                code.make(&OP_CONSTANT, &vec![0]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    )
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![1, 0]),
                    code.make(&OP_SET_GLOBAL, &vec![0]),
                    code.make(&OP_GET_GLOBAL, &vec![0]),
                    code.make(&OP_CALL, &vec![0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    let oneArg = fn(a) { a };
                    oneArg(24);
                "#.to_string(),
                expected_constants: vec![
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 1,
                            num_params: 1,
                            instructions: vec![
                                code.make(&OP_GET_LOCAL, &vec![0]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    ),
                    i_to_o(24),
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![0, 0]),
                    code.make(&OP_SET_GLOBAL, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_GET_GLOBAL, &vec![0]),
                    code.make(&OP_CALL, &vec![1]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    let manyArg = fn(a, b, c) { a; b; c };
                    manyArg(24, 25, 26);
                "#.to_string(),
                expected_constants: vec![
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 3,
                            num_params: 3,
                            instructions: vec![
                                code.make(&OP_GET_LOCAL, &vec![0]),
                                code.make(&OP_POP, &vec![]),
                                code.make(&OP_GET_LOCAL, &vec![1]),
                                code.make(&OP_POP, &vec![]),
                                code.make(&OP_GET_LOCAL, &vec![2]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    ),
                    i_to_o(24),
                    i_to_o(25),
                    i_to_o(26),
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![0, 0]),
                    code.make(&OP_SET_GLOBAL, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![1]),
                    code.make(&OP_CONSTANT, &vec![2]),
                    code.make(&OP_CONSTANT, &vec![3]),
                    code.make(&OP_GET_GLOBAL, &vec![0]),
                    code.make(&OP_CALL, &vec![3]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_let_statement_scopes() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    let num = 55;
                    fn() { num }
                "#.to_string(),
                expected_constants: vec![
                    i_to_o(55),
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 0,
                            num_params: 0,
                            instructions: vec![
                                code.make(&OP_GET_GLOBAL, &vec![0]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    )
                ],
                expected_instructions: vec![
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_SET_GLOBAL, &vec![0]),
                    code.make(&OP_CLOSURE, &vec![1, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    fn() {
                        let num = 55;
                        num
                    }
                "#.to_string(),
                expected_constants: vec![
                    i_to_o(55),
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 1,
                            num_params: 0,
                            instructions: vec![
                                code.make(&OP_CONSTANT, &vec![0]),
                                code.make(&OP_SET_LOCAL, &vec![0]),
                                code.make(&OP_GET_LOCAL, &vec![0]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    )
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![1, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    fn() {
                        let a = 55;
                        let b = 77;
                        a + b
                    }
                "#.to_string(),
                expected_constants: vec![
                    i_to_o(55),
                    i_to_o(77),
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 2,
                            num_params: 0,
                            instructions: vec![
                                code.make(&OP_CONSTANT, &vec![0]),
                                code.make(&OP_SET_LOCAL, &vec![0]),
                                code.make(&OP_CONSTANT, &vec![1]),
                                code.make(&OP_SET_LOCAL, &vec![1]),
                                code.make(&OP_GET_LOCAL, &vec![0]),
                                code.make(&OP_GET_LOCAL, &vec![1]),
                                code.make(&OP_ADD, &vec![]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    )
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![2, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }

    #[test]
    fn test_builtins() -> Result<()> {
        let code = MCode::new();
        let tests = vec![
            TestCase {
                input: r#"
                    len([]);
                    push([], 1);
                "#.to_string(),
                expected_constants: vec![i_to_o(1)],
                expected_instructions: vec![
                    code.make(&OP_ARRAY, &vec![0]),
                    code.make(&OP_GET_BUILTIN, &vec![0]),
                    code.make(&OP_CALL, &vec![1]),
                    code.make(&OP_POP, &vec![]),
                    code.make(&OP_ARRAY, &vec![0]),
                    code.make(&OP_CONSTANT, &vec![0]),
                    code.make(&OP_GET_BUILTIN, &vec![4]),
                    code.make(&OP_CALL, &vec![2]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
            TestCase {
                input: r#"
                    fn() { len([]) }
                "#.to_string(),
                expected_constants: vec![
                    MObject::CompiledFn(
                        CompiledFunction {
                            num_locals: 0,
                            num_params: 0,
                            instructions: vec![
                                code.make(&OP_ARRAY, &vec![0]),
                                code.make(&OP_GET_BUILTIN, &vec![0]),
                                code.make(&OP_CALL, &vec![1]),
                                code.make(&OP_RETURN_VAL, &vec![]),
                            ].into_iter().flatten().collect(),
                        }
                    )
                ],
                expected_instructions: vec![
                    code.make(&OP_CLOSURE, &vec![0, 0]),
                    code.make(&OP_POP, &vec![]),
                ],
            },
        ];

        run_compiler_tests(tests)
    }
}

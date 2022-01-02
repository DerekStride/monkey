use std::io::{self, Read, Write, BufRead, BufReader};

use crate::{
    lexer::lexer::Lexer,
    parser::parser::Parser,
    object::{MObject, NULL},
    interpreter::{
        evaluator,
        environment::Environment,
    },
    error::{Result, Error},
    compiler::{compiler::Compiler, vm::Vm, symbol_table::SymbolTable},
    ast::MNode,
};

#[derive(Debug)]
pub struct State {
    constants: Vec<MObject>,
    globals: Vec<MObject>,
    symbols: SymbolTable,
}

impl State {
    pub fn new() -> Self {
        Self {
            constants: Vec::new(),
            globals: Vec::new(),
            symbols: SymbolTable::new(),
        }
    }
}

#[derive(Debug)]
pub enum Env {
    Eval(Environment),
    Vm(State),
}

pub struct Engine {
    runner: fn(MNode, &mut Env) -> Result<MObject>,
    env: Env,
}

impl Engine {
    pub fn vm() -> Self {
        Self {
            runner: Self::vm_runner,
            env: Env::Vm(State::new()),
        }
    }

    pub fn eval() -> Self {
        Self {
            runner: Self::eval_runner,
            env: Env::Eval(Environment::new()),
        }
    }

    pub fn run(&mut self, node: MNode) -> Result<MObject> {
        (self.runner)(node, &mut self.env)
    }

    fn vm_runner(node: MNode, env: &mut Env) -> Result<MObject> {
        let state = match env {
            Env::Vm(x) => x,
            _ => return Err(Error::new(format!("wanted: Env::Vm, got: {:?}", env))),
        };

        let mut compiler = Compiler::with_state(state.symbols.clone(), state.constants.clone());
        compiler.compile(node)?;

        let code = compiler.bytecode();

        let mut vm = Vm::with_state(code.clone(), state.globals.clone());

        vm.run()?;

        state.symbols = compiler.symbol_table();
        state.constants = code.contstants;
        state.globals = vm.globals();

        match vm.stack_top() {
            Some(x) => Ok(x.clone()),
            None => Ok(NULL),
        }
    }

    fn eval_runner(node: MNode, env: &mut Env) -> Result<MObject> {
        if let Env::Eval(environment) = env {
            evaluator::eval(node, environment)
        } else {
            Err(Error::new(format!("wanted: Env::Eval, got: {:?}", env)))
        }
    }
}

const PROMPT: &[u8; 4] = b">>> ";

pub fn start<I: Read, O: Write>(input: I, output: &mut O, engine: &mut Engine) -> Result<()> {
    let mut bufio = BufReader::new(input);
    let mut buf = String::new();
    let mut macro_env = Environment::new();

    loop {
        output.write_all(PROMPT)?;
        output.flush()?;
        bufio.read_line(&mut buf)?;

        let src = buf.bytes().map(|x| Ok(x)).peekable();
        let lex = &mut Lexer::new(src)?;
        let mut parser = Parser::new(lex.peekable())?;
        let mut program = parser.parse()?;

        if let Err(_) = print_parser_errors(output, parser.errors()) {
            continue;
        };

        evaluator::define_macros(&mut program, &mut macro_env);
        let expanded = evaluator::expand_macros(program, &mut macro_env);

        let evaluated = engine.run(expanded)?;

        output.write_all(format!("{}\n", evaluated).as_bytes())?;
        output.flush()?;
        buf.clear()
    }
}

fn print_parser_errors<O: Write>(output: &mut O, errors: Vec<String>) -> io::Result<()> {
    if errors.is_empty() {
        return Ok(())
    }

    output.write_all(b"Parser errors:\n")?;
    for e in errors {
        output.write_all(format!("\t{}\n", e).as_bytes())?;
    }

    output.flush()
}

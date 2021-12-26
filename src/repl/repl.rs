use std::io::{self, Read, Write, BufRead, BufReader};

use crate::{
    lexer::lexer::Lexer,
    parser::parser::Parser,
    interpreter::{evaluator, environment::Environment, object::{MObject, NULL}},
    error::Result,
    compiler::{compiler::Compiler, vm::Vm},
    ast::MNode,
};

const PROMPT: &[u8; 4] = b">>> ";

pub fn start<I: Read, O: Write>(input: I, output: &mut O, engine: fn(MNode, &mut Environment) -> Result<MObject>) -> Result<()> {
    let mut bufio = BufReader::new(input);
    let mut buf = String::new();
    let mut env = Environment::new();
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

        let evaluated = engine(expanded, &mut env)?;

        output.write_all(format!("{}\n", evaluated).as_bytes())?;
        output.flush()?;
        buf.clear()
    }
}

pub fn vm(node: MNode, _: &mut Environment) -> Result<MObject> {
    let mut compiler = Compiler::new();
    compiler.compile(node)?;

    let mut vm = Vm::new(compiler.bytecode());

    vm.run()?;

    match vm.stack_top() {
        Some(x) => Ok(x.clone()),
        None => Ok(NULL),
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

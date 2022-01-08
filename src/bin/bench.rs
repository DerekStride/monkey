#![feature(div_duration)]

use monkey::{
    ast::*,
    error::{Result, Error},
    lexer::{
        lexer::Lexer,
        token::Token,
    },
    compiler::{
        vm::Vm,
        compiler::Compiler,
    },
    parser::parser::Parser,
    repl::Engine,
};

use std::{
    io::Read,
    time::Instant,
};

const INPUT: &'static str = r#"
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
fibonacci(28);
"#;

fn main() -> Result<()> {
    let program_vm = MNode::Prog(parse(INPUT.to_string())?);
    let mut eval = Engine::eval();
    let program_eval = MNode::Prog(parse(INPUT.to_string())?);

    let mut compiler = Compiler::new();
    compiler.compile(program_vm)?;
    let mut vm = Vm::new(compiler.bytecode());

    let func_str = INPUT
        .lines()
        .last()
        .unwrap();
    println!("Running:\n{}", func_str);

    let start = Instant::now();
    let result = fibonacci(28);
    let elapsed_eval = start.elapsed();
    println!("\nRust\nResult: {}", result);
    println!("Duration: {}.{}s", elapsed_eval.as_secs(), elapsed_eval.subsec_micros());

    let start = Instant::now();
    vm.run()?;
    let elapsed_vm = start.elapsed();
    println!("\nVm\nResult: {}", vm.stack_top().unwrap());
    println!("Duration: {}.{}s", elapsed_vm.as_secs(), elapsed_vm.subsec_micros());

    let start = Instant::now();
    let result = eval.run(program_eval)?;
    let elapsed_eval = start.elapsed();
    println!("\nEval\nResult: {}", result);
    println!("Duration: {}.{}s", elapsed_eval.as_secs(), elapsed_eval.subsec_micros());

    if elapsed_vm < elapsed_eval {
        println!("\nVm is {:.2}x faster than Eval", elapsed_eval.div_duration_f64(elapsed_vm))
    } else {
        println!("\nEval is {:.2}x faster than Vm", elapsed_vm.div_duration_f64(elapsed_eval))
    };

    Ok(())
}

fn fibonacci(x: u64) -> u64 {
    if x == 0 {
        0
    } else if x == 1 {
        1
    } else {
        fibonacci(x - 1) + fibonacci(x - 2)
    }
}

fn parse(input: String) -> Result<Program> {
    let lexer = Lexer::new(input.as_bytes().bytes().peekable())?;
    let mut parser = Parser::new(lexer.peekable())?;
    let program = parser.parse()?;

    check_parser_errors(parser)?;

    Ok(program)
}


fn check_parser_errors<I: Iterator<Item = Result<Token>>>(p: Parser<I>) -> Result<()> {
    let errors = p.errors();

    if errors.is_empty() { return Ok(()); };

    let mut msg = format!("The Parser had {} errors:\n", errors.len());

    for e in errors {
        msg.push_str(&e);
        msg.push('\n');
    }

    Err(Error::new(msg))
}

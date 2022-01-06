use monkey::{
    ast::*,
    error::{Result, Error},
    lexer::{
        lexer::Lexer,
        token::Token,
    },
    parser::parser::Parser,
    repl::Engine,
};

use std::{
    env,
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
fibonacci(15);
"#;

fn main() -> Result<()> {
    let mut vm = Engine::vm();
    let program_vm = MNode::Prog(parse(INPUT.to_string())?);
    let mut eval = Engine::eval();
    let program_eval = MNode::Prog(parse(INPUT.to_string())?);

    let start = Instant::now();
    vm.run(program_vm)?;
    let elapsed_vm = start.elapsed();
    println!("Vm:");
    println!("\t{}s", elapsed_vm.as_secs());
    println!("\t{}ms", elapsed_vm.as_millis());
    println!("\t{}us", elapsed_vm.as_micros());
    println!("\t{}ns", elapsed_vm.as_nanos());

    let start = Instant::now();
    eval.run(program_eval)?;
    let elapsed_eval = start.elapsed();
    println!("Eval:");
    println!("\t{}s", elapsed_eval.as_secs());
    println!("\t{}ms", elapsed_eval.as_millis());
    println!("\t{}us", elapsed_eval.as_micros());
    println!("\t{}ns", elapsed_eval.as_nanos());

    println!("Vm / Eval:");
    println!("\t{}", elapsed_vm.as_nanos() / elapsed_eval.as_nanos());
    Ok(())
}

pub fn parse(input: String) -> Result<Program> {
    let lexer = Lexer::new(input.as_bytes().bytes().peekable())?;
    let mut parser = Parser::new(lexer.peekable())?;
    let program = parser.parse()?;

    check_parser_errors(parser)?;

    Ok(program)
}


pub fn check_parser_errors<I: Iterator<Item = Result<Token>>>(p: Parser<I>) -> Result<()> {
    let errors = p.errors();

    if errors.is_empty() { return Ok(()); };

    let mut msg = format!("The Parser had {} errors:\n", errors.len());

    for e in errors {
        msg.push_str(&e);
        msg.push('\n');
    }

    Err(Error::new(msg))
}

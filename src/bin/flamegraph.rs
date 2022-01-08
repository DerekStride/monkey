use monkey::{
    repl::Engine,
    error::{Result, Error},
    ast::{
        MNode,
        Program,
    },
    lexer::{
        lexer::Lexer,
        token::Token,
    },
    parser::parser::Parser,
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
fibonacci(20);
"#;

fn main() -> Result<()> {
    let args = env::args();
    let program = MNode::Prog(parse(INPUT.to_string())?);

    let mut engine = if args.into_iter().any(|arg| arg == "--engine=vm") {
        Engine::vm()
    } else {
        Engine::eval()
    };

    let start = Instant::now();
    engine.run(program)?;
    let elapsed = start.elapsed();

    println!("Duration: {}.{}s", elapsed.as_secs(), elapsed.subsec_micros());

    Ok(())
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

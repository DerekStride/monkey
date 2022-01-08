#![feature(test)]

extern crate test;

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

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use monkey::{
        ast::*,
        error::{Result, Error},
        lexer::{
            lexer::Lexer,
            token::Token,
        },
        compiler::{compiler::Compiler, vm::Vm},
        parser::parser::Parser,
        repl::Engine,
    };

    use std::io::Read;

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

    #[bench]
    fn bench_compile(b: &mut Bencher) -> Result<()> {
        let program = MNode::Prog(parse(INPUT.to_string()).unwrap());
        let mut compiler = Compiler::new();

        b.iter(||
            assert!(compiler.compile(program.clone()).is_ok())
        );

        Ok(())
    }

    #[bench]
    fn bench_parse(b: &mut Bencher) -> Result<()> {
        b.iter(|| {
            parse(INPUT.to_string())
        });

        Ok(())
    }

    #[bench]
    fn bench_eval(b: &mut Bencher) -> Result<()> {
        let program = MNode::Prog(parse(INPUT.to_string())?);
        let mut engine = Engine::eval();

        b.iter(||
            engine.run(program.clone())
        );

        Ok(())
    }

    #[bench]
    fn bench_vm(b: &mut Bencher) -> Result<()> {
        let program = MNode::Prog(parse(INPUT.to_string()).unwrap());
        let mut compiler = Compiler::new();
        compiler.compile(program)?;

        b.iter(|| {
           let mut vm = Vm::new(compiler.bytecode());
            assert!(vm.run().is_ok());
        });

        Ok(())
    }

    #[bench]
    fn bench_rust(b: &mut Bencher) -> Result<()> {
        b.iter(||
            fibonacci(15)
        );

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
}

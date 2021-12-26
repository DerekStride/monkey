use std::{io, env};

mod interpreter;
mod parser;
mod error;
mod lexer;
mod compiler;
mod repl;
mod ast;

#[cfg(test)]
mod test_utils;

use crate::{
    interpreter::evaluator,
    repl::repl::{start, vm}
};

fn main() {
    let args = env::args();
    let input = io::stdin();
    let mut output = io::stdout();

    let engine = if args.into_iter().any(|arg| arg == "--engine=vm") {
        vm
    } else {
        evaluator::eval
    };

    start(input, &mut output, engine).unwrap();
}

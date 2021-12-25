use std::io;

mod interpreter;
mod parser;
mod error;
mod lexer;
mod compiler;
mod repl;
mod ast;

#[cfg(test)]
mod test_utils;

use crate::repl::repl::start;

fn main() {
    let input = io::stdin();
    let mut output = io::stdout();

    start(input, &mut output).unwrap();
}

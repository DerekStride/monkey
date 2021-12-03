use std::io;

mod parser;
mod error;
mod lexer;
mod repl;
mod ast;

use crate::repl::repl::start;


fn main() {
    let input = io::stdin();
    let mut output = io::stdout();

    start(input, &mut output).unwrap();
}

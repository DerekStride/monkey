use std::io;

mod error;
mod lexer;
mod repl;

use crate::repl::repl::start;


fn main() {
    let input = io::stdin();
    let mut output = io::stdout();

    start(input, &mut output).unwrap();
}

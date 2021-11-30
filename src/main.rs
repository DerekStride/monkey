use std::io::Read;

mod error;
mod lexer;

use crate::lexer::lexer::Lexer;

fn main() {
    let input = b"let five = 5;".to_vec();
    let lexer = &mut Lexer::new(input.bytes().peekable()).unwrap();
    println!("{:?}", lexer.next());
}

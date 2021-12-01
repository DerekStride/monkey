use std::io::{Read, Write, BufRead, BufReader};

use crate::{lexer::lexer::Lexer, error::Error};

const PROMPT: &[u8; 4] = b">>> ";

pub fn start<I: Read, O: Write>(input: I, output: &mut O) -> Result<(), Error> {
    let mut bufio = BufReader::new(input);
    let mut buf = String::new();

    loop {
        output.write_all(PROMPT)?;
        output.flush().unwrap();
        bufio.read_line(&mut buf)?;

        let src = buf.bytes().map(|x| Ok(x)).peekable();
        let lex = &mut Lexer::new(src)?;

        for tok in lex {
            output.write_all(format!("{:?}\n", tok?).as_bytes())?;
            output.flush()?;
        }
        buf.clear()
    }
}

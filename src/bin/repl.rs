use std::{io, env};

use monkey::repl::{start, Engine};

fn main() {
    let args = env::args();
    let input = io::stdin();
    let mut output = io::stdout();

    let mut engine = if args.into_iter().any(|arg| arg == "--engine=vm") {
        Engine::vm()
    } else {
        Engine::eval()
    };

    start(input, &mut output, &mut engine).unwrap();
}

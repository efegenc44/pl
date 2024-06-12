mod backend;
mod frontend;

use std::{
    env::args,
    fs::read_to_string,
    io::{self, stderr, stdin, stdout, Write},
};

use frontend::{parser::Parser, tokens::Tokens};

fn main() -> io::Result<()> {
    let args = &args().collect::<Vec<_>>()[..];
    match args {
        [_] => start_repl(),
        [_, file_path] => start_from_file(file_path),
        _ => write!(stderr(), "Too many arguments."),
    }
}

fn start_from_file(file_path: &str) -> io::Result<()> {
    let file = read_to_string(file_path)?;
    let ast = Parser::new(Tokens::new(file_path, &file))
        .expression()
        .unwrap();
    ast.data.pretty_print();
    Ok(())
}

fn start_repl() -> io::Result<()> {
    let mut stdout = stdout();
    let stdin = stdin();

    loop {
        write!(stdout, "> ")?;
        stdout.flush()?;

        let mut input = String::new();
        stdin.read_line(&mut input)?;
        let input = input.trim_end();

        match input {
            ".exit" => break Ok(()),
            "" => continue,
            _ => (),
        }

        let ast = Parser::new(Tokens::new("REPL", input))
            .expression()
            .unwrap();

        ast.data.pretty_print();
    }
}

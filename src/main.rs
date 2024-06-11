mod backend;
mod frontend;

use std::{
    env::args,
    fs::read_to_string,
    io::{self, stderr, Write},
};

use frontend::{parser::Parser, tokens::Tokens};

fn main() -> io::Result<()> {
    let args = &args().collect::<Vec<_>>()[..];
    let file_path = match args {
        [_, file_path] => file_path,
        _ => return write!(stderr(), "File path is not provided."),
    };

    let file = read_to_string(file_path)?;
    let ast = Parser::new(Tokens::new(file_path, &file))
        .expression()
        .unwrap();

    ast.data.pretty_print();
    Ok(())
}

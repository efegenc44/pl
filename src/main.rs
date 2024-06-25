mod backend;
mod frontend;

use std::{
    env::args,
    fs::read_to_string,
    io::{self, stderr, stdin, stdout, Write},
};

use backend::nameresolver::NameResolver;
use frontend::{parser::Parser, tokens::Tokens};

fn main() -> io::Result<()> {
    let args = &args().collect::<Vec<_>>()[..];
    match args {
        [_] => start_repl(),
        [_, file_path] => start_from_file(file_path),
        // TODO: Proper error reporting.
        _ => write!(stderr(), "Too many arguments."),
    }
}

fn start_from_file(file_path: &str) -> io::Result<()> {
    let file = read_to_string(file_path)?;
    let module = match Parser::new(Tokens::new(&file)).module() {
        Ok(program) => program,
        Err(err) => {
            return err.report(file_path, &read_to_string(file_path)?);
        }
    };

    let resolved_program = match NameResolver::new().resolve_names_in_module(module) {
        Ok(resolved_program) => resolved_program,
        Err(err) => {
            let file = read_to_string(file_path)?;
            return err.report(file_path, &file);
        }
    };

    for decl in resolved_program.decls {
        decl.1.pretty_print();
    }

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

        let ast = match Parser::new(Tokens::new(input)).expression() {
            Ok(ast) => ast,
            Err(err) => {
                err.report("REPL", input)?;
                continue;
            }
        };

        let resolved_ast = match NameResolver::new().resolve_names_in_expr(ast) {
            Ok(resolved_ast) => resolved_ast,
            Err(err) => {
                err.report("REPL", input)?;
                continue;
            }
        };
        resolved_ast.pretty_print();
    }
}

mod backend;
mod frontend;

use std::{
    env::args,
    fs::read_to_string,
    io::{self, stderr, stdin, stdout, Write}, path::PathBuf,
};

use backend::{evaluator::Evaluator, module::Module, nameresolver::NameResolver, typechecker::TypeChecker};
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

    let pathbuf = PathBuf::from(file_path);
    let file_name = pathbuf.file_name().unwrap().to_os_string().into_string().unwrap().into_boxed_str();
    let declarations = match Parser::new(Tokens::new(&file), pathbuf).declarations() {
        Ok(declarations) => declarations,
        Err(error) => return error.report(file_path, &read_to_string(file_path)?)
    };

    let module = match Module::new(declarations, file_name) {
        Ok(module) => module,
        Err(error) => return error.report(file_path, &read_to_string(file_path)?)
    };

    let resolved_module = match NameResolver::resolve_module(module) {
        Ok(resolved_module) => resolved_module,
        Err(error) => return error.report(file_path, &read_to_string(file_path)?)
    };

    if let Err(error) = TypeChecker::new(&resolved_module).type_check_module(&resolved_module) {
        return error.report(file_path, &read_to_string(file_path)?)
    };

    let value = Evaluator::eval_module_from_main(&resolved_module);

    println!(" = {value}");
    Ok(())
}

fn start_repl() -> io::Result<()> {
    let mut stdout = stdout();
    let stdin = stdin();
    let module = Module::default();
    let mut resolver = NameResolver::new(&module);
    let mut type_checker = TypeChecker::new(&module);
    let mut evaluator = Evaluator::new(&module);

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

        let expression = match Parser::new(Tokens::new(input), PathBuf::new()).expression() {
            Ok(expression) => expression,
            Err(error) => {
                error.report("REPL", input)?;
                continue;
            }
        };

        let resolved_expression = match resolver.resolve_expr(expression) {
            Ok(resolved_expression) => resolved_expression,
            Err(error) => {
                error.report("REPL", input)?;
                continue;
            }
        };

        let typ = match type_checker.type_check_expr(&resolved_expression) {
            Ok(typ) => typ,
            Err(error) => {
                error.report("REPL", input)?;
                continue;
            }
        };

        let value = evaluator.eval_expr(&resolved_expression);

        println!(" {value} : {typ}")
    }
}

// TODO: implement importing from the upper module (super::)

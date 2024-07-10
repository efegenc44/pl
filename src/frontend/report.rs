use std::{
    fmt::Display,
    fs::read_to_string,
    io::{self, stderr, Write},
};

use crate::backend::{module::ModuleError, nameresolver::ResolutionError, typechecker::TypeCheckError};

use super::{parser::ParseError, span::Spanned};

fn report_unexpected_eof(error: &Spanned<ParseError>, source_name: &str) -> io::Result<()> {
    let mut stderr = stderr();
    writeln!(stderr)?;
    writeln!(stderr, "  Error | [{source_name}] (at parsing)",)?;
    writeln!(stderr, "        |")?;
    writeln!(stderr, "        | {}\n", error.data)
}

fn report<E: Display>(
    error: &Spanned<E>,
    source_name: &str,
    source: &str,
    stage: &str,
) -> io::Result<()> {
    let mut lines = source.lines();
    let mut stderr = stderr();

    let row_start = error.span.start.row;
    let row_end = error.span.end.row;
    let col_start = error.span.start.col;
    let col_end = error.span.end.col;

    writeln!(stderr)?;
    writeln!(
        stderr,
        "  Error | [{source_name}:{row_start}:{col_start}] (at {stage})"
    )?;
    writeln!(stderr, "        |")?;

    let first_line = lines.nth(row_start - 1).unwrap();
    writeln!(stderr, "   {row_start:>4} | {first_line}")?;
    write!(stderr, "        | {}", " ".repeat(col_start - 1))?;

    if row_start == row_end {
        writeln!(stderr, "{}", "^".repeat(col_end - col_start))?;
    } else {
        writeln!(stderr, "{}", "^".repeat(first_line.len() + 1 - col_start))?;

        for row_middle in row_start + 1..row_end {
            let line = lines.next().unwrap();
            writeln!(stderr, "   {row_middle:>4} | {line}")?;
            writeln!(stderr, "        | {}", "^".repeat(line.len()))?;
        }

        let last_line = lines.next().unwrap();
        writeln!(stderr, "   {row_end:>4} | {last_line}")?;
        writeln!(stderr, "        | {}", "^".repeat(col_end - 1))?;
    }
    writeln!(stderr, "        | {}\n", error.data)
}

impl Spanned<ParseError> {
    pub fn report(&self, source_name: &str, source: &str) -> io::Result<()> {
        match &self.data {
            ParseError::UnexpectedEOF => report_unexpected_eof(self, source_name),
            ParseError::ImportError { import_path, error } => {
                report(self, source_name, source, "parsing")?;
                error.report(import_path, &read_to_string(import_path.as_ref())?)
            }
            _ => report(self, source_name, source, "parsing"),
        }
    }
}

impl Spanned<ResolutionError> {
    pub fn report(&self, source_name: &str, source: &str) -> io::Result<()> {
        match &self.data {
            ResolutionError::ImportError { import_path, error } => {
                report(self, source_name, source, "name resolution")?;
                error.report(import_path, &read_to_string(import_path.as_ref())?)
            }
            _ => report(self, source_name, source, "name resolution"),
        }
    }
}

impl Spanned<TypeCheckError> {
    pub fn report(&self, source_name: &str, source: &str) -> io::Result<()> {
        match &self.data {
            TypeCheckError::ImportError { import_path, error } => {
                report(self, source_name, source, "type checking")?;
                error.report(import_path, &read_to_string(import_path.as_ref())?)
            }
            _ => report(self, source_name, source, "type checking"),
        }
    }
}

impl Spanned<ModuleError> {
    pub fn report(&self, source_name: &str, source: &str) -> io::Result<()> {
        match &self.data {
            ModuleError::ImportError { import_path, error } => {
                report(self, source_name, source, "module creation")?;
                error.report(import_path, &read_to_string(import_path.as_ref())?)
            }
            _ => report(self, source_name, source, "module creation"),
        }
    }
}

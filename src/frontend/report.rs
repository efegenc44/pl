use std::{
    fmt::Display,
    io::{self, stderr, Write},
};

use crate::backend::nameresolver::ResolutionError;

use super::{parser::ParseError, span::Spanned};

fn report_unexpected_eof<'source>(error: &Spanned<'source, ParseError<'source>>) -> io::Result<()> {
    let mut stderr = stderr();
    writeln!(stderr)?;
    writeln!(
        stderr,
        "  Error | [{}] (at parsing)",
        error.span.source_name
    )?;
    writeln!(stderr, "        |")?;
    writeln!(stderr, "        | {}\n", error.data)
}

fn report<E: Display>(error: &Spanned<E>, source: &str, stage: &str) -> io::Result<()> {
    let mut lines = source.lines();
    let mut stderr = stderr();

    let source_name = error.span.source_name;
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

impl<'source> Spanned<'source, ParseError<'source>> {
    pub fn report(&self, source: &'source str) -> io::Result<()> {
        if matches!(self.data, ParseError::UnexpectedEOF) {
            report_unexpected_eof(self)
        } else {
            report(self, source, "parsing")
        }
    }
}

impl<'source> Spanned<'source, ResolutionError<'source>> {
    pub fn report(&self, source: &'source str) -> io::Result<()> {
        report(self, source, "name resolution")
    }
}

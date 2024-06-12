use std::fmt::Display;

#[derive(Debug, Clone, Copy)]
pub struct Span<'source> {
    pub source_name: &'source str,
    pub start: FilePosition,
    pub end: FilePosition,
}

impl<'source> Span<'source> {
    pub fn new(source_name: &'source str, start: FilePosition, end: FilePosition) -> Self {
        Self {
            source_name,
            start,
            end,
        }
    }

    pub fn extend(self, other: Self) -> Self {
        Self {
            source_name: self.source_name,
            start: self.start,
            end: other.end,
        }
    }

    pub fn eof(source_name: &'source str) -> Self {
        Self {
            source_name,
            start: FilePosition::new(0, 0),
            end: FilePosition::new(0, 0),
        }
    }
}

impl Display for Span<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{} - {}:{}",
            self.source_name, self.start, self.source_name, self.end
        )
    }
}

#[derive(Debug)]
pub struct Spanned<'source, T> {
    pub data: T,
    pub span: Span<'source>,
}

impl<'source, T> Spanned<'source, T> {
    pub fn new(data: T, span: Span<'source>) -> Self {
        Self { data, span }
    }
}

impl<T: Display> Display for Spanned<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:<15} [{}]", format!("{}", self.data), self.span)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FilePosition {
    pub row: usize,
    pub col: usize,
}

impl FilePosition {
    pub fn new(row: usize, col: usize) -> Self {
        Self { row, col }
    }
}

impl Display for FilePosition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.row, self.col)
    }
}

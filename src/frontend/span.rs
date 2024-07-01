use std::fmt::Display;

#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: FilePosition,
    pub end: FilePosition,
}

impl Span {
    pub fn new(start: FilePosition, end: FilePosition) -> Self {
        Self { start, end }
    }

    pub fn extend(self, other: Self) -> Self {
        Self {
            start: self.start,
            end: other.end,
        }
    }

    pub fn eof() -> Self {
        Self {
            start: FilePosition::new(0, 0),
            end: FilePosition::new(0, 0),
        }
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ":{} - :{}", self.start, self.end)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Spanned<T> {
    pub data: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(data: T, span: Span) -> Self {
        Self { data, span }
    }
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:<15} [{}]", format!("{}", self.data), self.span)
    }
}

pub trait HasSpan {
    fn attach(self, span: Span) -> Spanned<Self>
    where
        Self: Sized,
    {
        Spanned::new(self, span)
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

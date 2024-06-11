use std::fmt::Display;

pub struct Span<'source> {
    source_name: &'source str,
    start: FilePosition,
    end: FilePosition,
}

impl<'source> Span<'source> {
    pub fn new(source_name: &'source str, start: FilePosition, end: FilePosition) -> Self {
        Self {
            source_name,
            start,
            end,
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

pub struct Spanned<'source, T> {
    data: T,
    span: Span<'source>,
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

pub struct FilePosition {
    row: usize,
    col: usize,
}

impl FilePosition {
    pub fn new(row: usize, col: usize) -> Self {
        Self { row, col }
    }
}

impl Display for FilePosition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.col, self.row)
    }
}

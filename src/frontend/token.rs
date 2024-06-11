use std::fmt::Display;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Token<'source> {
    Identifier(&'source str),
    Integer(&'source str),
    Float(&'source str),
    String(&'source str),
    Operator(&'source str),
    OpeningParenthesis,
    ClosingParenthesis,
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier(lexeme)
            | Self::Integer(lexeme)
            | Self::Float(lexeme)
            | Self::String(lexeme)
            | Self::Operator(lexeme) => {
                write!(f, "{lexeme}")
            }
            Self::OpeningParenthesis => write!(f, "("),
            Self::ClosingParenthesis => write!(f, ")"),
        }
    }
}

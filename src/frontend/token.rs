use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token<'source> {
    Identifier(&'source str),
    Integer(&'source str),
    Float(&'source str),
    String(&'source str),
    OpeningParenthesis,
    ClosingParenthesis,
    Comma,
    Dot,
    Equals,
    Backslash,
    Minus,
    Plus,
    Star,
    Carrot,
    Less,
    RightArrow,
    KeywordLet,
    KeywordIn,
    KeywordFunc,
    KeywordImport,
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier(lexeme)
            | Self::Integer(lexeme)
            | Self::Float(lexeme)
            | Self::String(lexeme) => {
                write!(f, "{lexeme}")
            }
            Self::OpeningParenthesis => write!(f, "("),
            Self::ClosingParenthesis => write!(f, ")"),
            Self::Comma => write!(f, ","),
            Self::Dot => write!(f, "."),
            Self::Equals => write!(f, "="),
            Self::Minus => write!(f, "-"),
            Self::Plus => write!(f, "+"),
            Self::Star => write!(f, "*"),
            Self::Carrot => write!(f, "^"),
            Self::Less => write!(f, "<"),
            Self::Backslash => write!(f, "\\"),
            Self::RightArrow => write!(f, "->"),
            Self::KeywordLet => write!(f, "let"),
            Self::KeywordIn => write!(f, "in"),
            Self::KeywordFunc => write!(f, "func"),
            Self::KeywordImport => write!(f, "import"),
        }
    }
}

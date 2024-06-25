use std::fmt::Display;

pub type Symbol = Box<str>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Identifier(Symbol),
    Integer(Symbol),
    Float(Symbol),
    String(Symbol),
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
    Colon,
    DoubleColon,
    KeywordLet,
    KeywordIn,
    KeywordFunc,
    KeywordImport,
    KeywordNothing,
}

impl Display for Token {
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
            Self::Colon => write!(f, ":"),
            Self::DoubleColon => write!(f, "::"),
            Self::KeywordLet => write!(f, "let"),
            Self::KeywordIn => write!(f, "in"),
            Self::KeywordFunc => write!(f, "func"),
            Self::KeywordImport => write!(f, "import"),
            Self::KeywordNothing => write!(f, "nothing"),
        }
    }
}

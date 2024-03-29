use std::{fmt, iter::Peekable, str::Chars};

use crate::ranged::Ranged;

pub struct Tokens<'source> {
    chars: Peekable<Chars<'source>>,
    col: usize,
    row: usize,
}

impl<'source> Tokens<'source> {
    pub fn new(source: &'source str) -> Self {
        Self {
            chars: source.chars().peekable(),
            col: 1,
            row: 1,
        }
    }

    fn two_char_token(&mut self, expected: char, then: Token, otherwise: Token) -> Token {
        if self.chars.next_if_eq(&expected).is_some() {
            self.col += 1;
            then
        } else {
            otherwise
        }
    }

    fn number(&mut self) -> Token {
        let mut number = String::new();
        while let Some(ch) = self.chars.next_if(|ch| ch.is_ascii_digit()) {
            self.col += 1;
            number.push(ch);
        }

        Token::NaturalNumber(number)
    }

    fn symbol(&mut self) -> Token {
        let mut symbol = String::new();
        while let Some(ch) = self.chars.next_if(|ch| ch.is_alphanumeric()) {
            self.col += 1;
            symbol.push(ch);
        }

        match symbol.as_str() {
            "let" => Token::LetKeyword,
            "in" => Token::InKeyword,
            "import" => Token::ImportKeyword,
            "match" => Token::MatchKeyword,
            "true" => Token::TrueKeyword,
            "false" => Token::FalseKeyword,
            "and" => Token::AndKeyword,
            "or" => Token::OrKeyword,
            "if" => Token::IfKeyword,
            "then" => Token::ThenKeyword,
            "else" => Token::ElseKeyword,
            "mod" => Token::ModKeyword,
            _ => Token::Identifier(symbol),
        }
    }
}

impl Iterator for Tokens<'_> {
    type Item = Result<Ranged<Token>, Ranged<TokenError>>;

    fn next(&mut self) -> Option<Self::Item> {
        let Some(&ch) = self.chars.peek() else {
            return None;
        };

        let col_start = self.col;
        let row_start = self.row;

        if ch.is_whitespace() {
            if ch == '\n' {
                self.col = 1;
                self.row += 1;
            } else {
                self.col += 1;
            }
            self.chars.next();
            return self.next();
        }

        if ch.is_alphabetic() {
            return Some(Ok(Ranged::new(
                self.symbol(),
                ((col_start, row_start), (self.col, self.row)),
            )));
        }

        if ch.is_ascii_digit() {
            return Some(Ok(Ranged::new(
                self.number(),
                ((col_start, row_start), (self.col, self.row)),
            )));
        }

        self.chars.next();
        self.col += 1;
        let token = match ch {
            '(' => Token::OpeningParenthesis,
            ')' => Token::ClosingParenthesis,
            '*' => Token::Asterisk,
            '\\' => Token::Backslash,
            '<' => self.two_char_token('=', Token::LessEquals, Token::Less),
            '>' => self.two_char_token('=', Token::GreaterEquals, Token::Greater),
            '=' => self.two_char_token('=', Token::DoubleEquals, Token::Equals),
            '-' => self.two_char_token('>', Token::Arrow, Token::Minus),
            '/' => self.two_char_token('=', Token::SlashEquals, Token::Slash),
            ':' => Token::Colon,
            ',' => Token::Comma,
            '+' => Token::Plus,
            '.' => Token::Dot,
            '|' => Token::Bar,
            _ => {
                return Some(Err(Ranged::new(
                    TokenError::UnknownStartOfAToken(ch),
                    ((col_start, row_start), (self.col, self.row)),
                )))
            }
        };

        Some(Ok(Ranged::new(
            token,
            ((col_start, row_start), (self.col, self.row)),
        )))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Identifier(String),
    NaturalNumber(String),
    OpeningParenthesis,
    ClosingParenthesis,
    GreaterEquals,
    DoubleEquals,
    SlashEquals,
    LessEquals,
    Backslash,
    Asterisk,
    Greater,
    Equals,
    Slash,
    Arrow,
    Colon,
    Comma,
    Minus,
    Plus,
    Less,
    Bar,
    Dot,
    LetKeyword,
    InKeyword,
    ImportKeyword,
    MatchKeyword,
    TrueKeyword,
    FalseKeyword,
    AndKeyword,
    OrKeyword,
    IfKeyword,
    ThenKeyword,
    ElseKeyword,
    ModKeyword,
}

#[derive(Clone, Debug)]
pub enum TokenError {
    UnknownStartOfAToken(char),
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownStartOfAToken(ch) => write!(f, "`{ch}` is not the start of a token."),
        }
    }
}

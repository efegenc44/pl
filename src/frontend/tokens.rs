use std::{iter::Peekable, str::CharIndices};

use crate::frontend::span::Span;

use super::{
    span::{FilePosition, Spanned},
    token::Token,
};

pub struct Tokens<'source> {
    source_name: &'source str,
    source: &'source str,
    chars: Peekable<CharIndices<'source>>,
    row: usize,
    col: usize,
}

impl<'source> Tokens<'source> {
    pub fn new(source_name: &'source str, source: &'source str) -> Self {
        Self {
            source_name,
            source,
            chars: source.char_indices().peekable(),
            row: 1,
            col: 1,
        }
    }

    fn current_position(&self) -> FilePosition {
        FilePosition::new(self.row, self.col)
    }

    fn current_indice(&mut self) -> usize {
        if let Some((indice, _)) = self.chars.peek() {
            *indice
        } else {
            self.source.len()
        }
    }

    fn continuously_advance<F>(&mut self, f: F)
    where
        F: Fn(&char) -> bool,
    {
        while self.chars.next_if(|(_, ch)| f(ch)).is_some() {
            self.col += 1;
        }
    }

    fn single_char(&mut self, token: Token<'source>) -> Token<'source> {
        self.chars.next();
        self.col += 1;
        token
    }

    fn double_char(
        &mut self,
        single: Token<'source>,
        ch: char,
        double: Token<'source>,
    ) -> Token<'source> {
        self.chars.next();
        self.col += 1;
        if self.chars.next_if(|(_, next)| next == &ch).is_some() {
            self.col += 1;
            double
        } else {
            single
        }
    }

    fn keyword_or_identifier(&mut self) -> Spanned<'source, Token<'source>> {
        let start_indice = self.current_indice();
        let start_position = self.current_position();
        self.continuously_advance(|ch| ch.is_alphanumeric() || ['_', '\''].contains(ch));
        let end_position = self.current_position();
        let end_indice = self.current_indice();

        let token = match &self.source[start_indice..end_indice] {
            "let" => Token::KeywordLet,
            "in" => Token::KeywordIn,
            identifier => Token::Identifier(identifier),
        };
        Spanned::new(
            token,
            Span::new(self.source_name, start_position, end_position),
        )
    }

    fn numeric(&mut self) -> Spanned<'source, Token<'source>> {
        let start_indice = self.current_indice();
        let start_position = self.current_position();
        self.continuously_advance(|ch| ch.is_ascii_digit() || ch == &'_');
        let constructor = if self.chars.next_if(|(_, ch)| ch == &'.').is_some() {
            self.col += 1;
            self.continuously_advance(|ch| ch.is_ascii_digit() || ch == &'_');
            Token::Float
        } else {
            Token::Integer
        };

        let end_position = self.current_position();
        let end_indice = self.current_indice();

        let lexeme = &self.source[start_indice..end_indice];
        Spanned::new(
            constructor(lexeme),
            Span::new(self.source_name, start_position, end_position),
        )
    }

    fn string(&mut self) -> Spanned<'source, Token<'source>> {
        let start_indice = self.current_indice();
        let start_position = self.current_position();
        self.chars.next(); // Skip the first '"'.
        self.col += 1;
        while let Some((_, ch)) = self.chars.next_if(|(_, ch)| ch != &'"') {
            if ch == '\n' {
                self.col = 1;
                self.row += 1;
            } else {
                self.col += 1;
            }
        }

        let Some((_, '"')) = self.chars.next() else {
            todo!("Unterminated string literal.")
        };
        self.row += 1;
        let end_position = self.current_position();
        let end_indice = self.current_indice();

        let lexeme = &self.source[start_indice..end_indice];
        Spanned::new(
            Token::String(lexeme),
            Span::new(self.source_name, start_position, end_position),
        )
    }

    fn symbol(&mut self) -> Spanned<'source, Token<'source>> {
        let start_position = self.current_position();
        let token = match self.chars.peek().unwrap().1 {
            '(' => self.single_char(Token::OpeningParenthesis),
            ')' => self.single_char(Token::ClosingParenthesis),
            ',' => self.single_char(Token::Comma),
            '=' => self.single_char(Token::Equals),
            '+' => self.single_char(Token::Plus),
            '*' => self.single_char(Token::Star),
            '^' => self.single_char(Token::Carrot),
            '<' => self.single_char(Token::Less),
            '\\' => self.single_char(Token::Backslash),
            '-' => self.double_char(Token::Minus, '>', Token::RightArrow),
            _ => todo!("Unknown start of a token."),
        };
        let end_position = self.current_position();

        Spanned::new(
            token,
            Span::new(self.source_name, start_position, end_position),
        )
    }

    pub fn source_name(&self) -> &'source str {
        self.source_name
    }
}

impl<'source> Iterator for Tokens<'source> {
    type Item = Spanned<'source, Token<'source>>;

    fn next(&mut self) -> Option<Self::Item> {
        // Skip whitespaces.
        while let Some((_, ch)) = self.chars.next_if(|(_, ch)| ch.is_whitespace()) {
            if ch == '\n' {
                self.col = 1;
                self.row += 1;
            } else {
                self.col += 1;
            }
        }

        let Some((_, ch)) = self.chars.peek() else {
            return None;
        };

        Some(if ch.is_alphabetic() {
            self.keyword_or_identifier()
        } else if ch.is_ascii_digit() {
            self.numeric()
        } else if ch == &'"' {
            self.string()
        } else {
            self.symbol()
        })
    }
}

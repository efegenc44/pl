use std::{fmt::Display, iter::Peekable};

use crate::{
    backend::ast::{Bound, Expression, Operator, Pattern},
    frontend::token::Token,
};

use super::{
    span::{HasSpan, Span, Spanned},
    tokens::Tokens,
};

#[derive(PartialEq)]
enum Associativity {
    Right,
    Left,
    None,
}

const OPERATORS: [(Token, Associativity, usize); 5] = [
    (Token::Less, Associativity::None, 0),
    (Token::Plus, Associativity::Left, 1),
    (Token::Minus, Associativity::Left, 1),
    (Token::Star, Associativity::Left, 2),
    (Token::Carrot, Associativity::Right, 3),
];

pub struct Parser<'source> {
    source_name: &'source str,
    tokens: Peekable<Tokens<'source>>,
}

impl<'source> Parser<'source> {
    pub fn new(tokens: Tokens<'source>) -> Self {
        Self {
            source_name: tokens.source_name(),
            tokens: tokens.peekable(),
        }
    }

    fn unexpected_eof<T>(&self) -> ParseResult<'source, T> {
        Err(ParseError::UnexpectedEOF.attach(Span::eof(self.source_name)))
    }

    fn expect(&mut self, expected: Token) -> ParseResult<'source, Span<'source>> {
        let Some(spanned_token) = self.tokens.next() else {
            return self.unexpected_eof()
        };

        if spanned_token.data == expected {
            Ok(spanned_token.span)
        } else {
            Err(ParseError::UnexpectedToken(spanned_token.data).attach(spanned_token.span))
        }
    }

    fn peek_is(&mut self, expected: Token) -> bool {
        self.tokens
            .peek()
            .map_or(false, |peeked| peeked.data == expected)
    }

    fn comma_seperated_until<T, F>(
        &mut self,
        f: F,
        until: Token<'source>,
    ) -> ParseResult<'source, Vec<T>>
    where
        F: Fn(&mut Self) -> ParseResult<'source, T>,
    {
        let mut things = vec![];
        if !self.peek_is(until) {
            things.push(f(self)?);
            while !self.peek_is(until) {
                self.expect(Token::Comma)?;
                things.push(f(self)?);
            }
        }

        Ok(things)
    }

    fn literal<T, F>(
        &mut self,
        constructor: F,
        lexeme: &'source str,
        span: Span<'source>,
    ) -> ParseResult<'source, Spanned<'source, T>>
    where
        T: HasSpan,
        F: Fn(&'source str) -> T,
    {
        let thing = constructor(lexeme).attach(span);
        self.tokens.next();
        Ok(thing)
    }

    fn grouping(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let start = self.expect(Token::OpeningParenthesis)?;
        let expr = self.expression()?;
        let end = self.expect(Token::ClosingParenthesis)?;

        Ok(expr.data.attach(start.extend(end)))
    }

    fn pattern_grouping(&mut self) -> ParseResult<'source, Spanned<'source, Pattern<'source>>> {
        let start = self.expect(Token::OpeningParenthesis)?;
        let expr = self.pattern()?;
        let end = self.expect(Token::ClosingParenthesis)?;

        Ok(expr.data.attach(start.extend(end)))
    }

    fn lett(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let start = self.expect(Token::KeywordLet)?;
        let pattern = self.pattern()?;
        self.expect(Token::Equals)?;
        let expr = self.expression()?;
        self.expect(Token::KeywordIn)?;
        let body = self.expression()?;
        let end = body.span;

        Ok(Expression::Let {
            pattern,
            expr: Box::new(expr),
            body: Box::new(body),
        }
        .attach(start.extend(end)))
    }

    fn lambda(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let start = self.expect(Token::Backslash)?;
        let params = self.comma_seperated_until(Self::pattern, Token::RightArrow)?;
        self.expect(Token::RightArrow)?;
        let body = self.expression()?;
        let end = body.span;

        Ok(Expression::Lambda {
            params,
            body: Box::new(body),
        }
        .attach(start.extend(end)))
    }

    fn pattern(&mut self) -> ParseResult<'source, Spanned<'source, Pattern<'source>>> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        let span = peeked.span;
        match peeked.data {
            Token::Identifier(identifier) => self.literal(Pattern::Any, identifier, span),
            Token::Integer(integer) => self.literal(Pattern::Integer, integer, span),
            Token::Float(float) => self.literal(Pattern::Float, float, span),
            Token::String(string) => self.literal(Pattern::String, string, span),
            Token::OpeningParenthesis => self.pattern_grouping(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected).attach(span)),
        }
    }

    fn primary(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        let span = peeked.span;
        match peeked.data {
            Token::Identifier(identifier) => {
                let expr = Expression::Identifier(identifier, Bound::None).attach(span);
                self.tokens.next();
                Ok(expr)
            }
            Token::Integer(integer) => self.literal(Expression::Integer, integer, span),
            Token::Float(float) => self.literal(Expression::Float, float, span),
            Token::String(string) => self.literal(Expression::String, string, span),
            Token::OpeningParenthesis => self.grouping(),
            Token::KeywordLet => self.lett(),
            Token::Backslash => self.lambda(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected).attach(span)),
        }
    }

    fn application(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let mut expr = self.primary()?;

        while let Some(Token::OpeningParenthesis) = self.tokens.peek().map(|peeked| &peeked.data) {
            self.tokens.next();
            let args = self.comma_seperated_until(Self::expression, Token::ClosingParenthesis)?;
            let end = self.expect(Token::ClosingParenthesis)?;

            let span = expr.span.extend(end);
            expr = Expression::Application {
                expr: Box::new(expr),
                args,
            }
            .attach(span)
        }

        Ok(expr)
    }

    fn binary(
        &mut self,
        min_precedence: usize,
    ) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let mut lhs = self.application()?;

        while let Some(token) = self.tokens.peek().map(|peeked| &peeked.data) {
            let Some((op, assoc, op_precedence)) = OPERATORS.iter().find(|(op, _, _)| op == token) else {
                break;
            };

            let op = match op {
                Token::Minus => Operator::Sub,
                Token::Plus => Operator::Add,
                Token::Star => Operator::Mul,
                Token::Carrot => Operator::Pow,
                Token::Less => Operator::Less,
                _ => unreachable!(),
            };

            if op_precedence < &min_precedence {
                break;
            }
            self.tokens.next();

            let rhs = self.binary(op_precedence + usize::from(assoc != &Associativity::Right))?;

            let span = lhs.span.extend(rhs.span);
            lhs = Expression::Binary {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
            .attach(span);

            if assoc == &Associativity::None {
                break;
            }
        }

        Ok(lhs)
    }

    pub fn expression(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        self.binary(0)
    }
}

#[derive(Debug)]
pub enum ParseError<'source> {
    UnexpectedEOF,
    UnexpectedToken(Token<'source>),
}

impl<'source> ParseError<'source> {
    fn attach(self, span: Span<'source>) -> Spanned<'source, Self> {
        Spanned::new(self, span)
    }
}

impl Display for ParseError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEOF => write!(f, "Unexpected EOF."),
            Self::UnexpectedToken(unexpected) => write!(f, "Unexpected token: `{unexpected}`."),
        }
    }
}

type ParseResult<'a, T> = Result<T, Spanned<'a, ParseError<'a>>>;

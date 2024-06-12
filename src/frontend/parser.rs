use std::iter::Peekable;

use crate::{
    backend::ast::{Expression, Pattern},
    frontend::token::Token,
};

use super::{
    span::{Span, Spanned},
    tokens::Tokens,
};

#[derive(PartialEq)]
enum Associativity {
    Right,
    Left,
    None,
}

const OPERATORS: [(&str, Associativity, usize); 4] = [
    ("<", Associativity::None, 0),
    ("+", Associativity::Left, 1),
    ("*", Associativity::Left, 2),
    ("^", Associativity::Right, 3),
];

pub struct Parser<'source> {
    tokens: Peekable<Tokens<'source>>,
}

impl<'source> Parser<'source> {
    pub fn new(tokens: Tokens<'source>) -> Self {
        Self {
            tokens: tokens.peekable(),
        }
    }

    fn expect(&mut self, expected: Token) -> ParseResult<'source, Span<'source>> {
        let Some(spanned_token) = self.tokens.next() else {
            return Err(ParseError::UnexpectedEOF);
        };

        if spanned_token.data == expected {
            Ok(spanned_token.span)
        } else {
            Err(ParseError::UnexpectedToken(spanned_token.data))
        }
    }

    fn peek_is(&mut self, expected: Token) -> bool {
        self.tokens
            .peek()
            .map_or(false, |peeked| peeked.data == expected)
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
        self.expect(Token::Operator("="))?;
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
        let start = self.expect(Token::Operator("\\"))?;
        let mut params = vec![];
        if !self.peek_is(Token::Operator("->")) {
            params.push(self.pattern()?);
            while !self.peek_is(Token::Operator("->")) {
                self.expect(Token::Comma)?;
                params.push(self.pattern()?);
            }
        }
        self.expect(Token::Operator("->"))?;
        let body = self.expression()?;
        let end = body.span;

        Ok(Expression::Lambda {
            params,
            body: Box::new(body),
        }
        .attach(start.extend(end)))
    }

    fn pattern(&mut self) -> ParseResult<'source, Spanned<'source, Pattern<'source>>> {
        let Some(spanned_token) = self.tokens.peek() else {
            return Err(ParseError::UnexpectedEOF)
        };

        match &spanned_token.data {
            Token::Identifier(identifier) => {
                let pattern = Pattern::Any(identifier).attach(spanned_token.span);
                self.tokens.next();
                Ok(pattern)
            }
            Token::Integer(integer) => {
                let pattern = Pattern::Integer(integer).attach(spanned_token.span);
                self.tokens.next();
                Ok(pattern)
            }
            Token::Float(float) => {
                let pattern = Pattern::Float(float).attach(spanned_token.span);
                self.tokens.next();
                Ok(pattern)
            }
            Token::String(string) => {
                let pattern = Pattern::String(string).attach(spanned_token.span);
                self.tokens.next();
                Ok(pattern)
            }
            Token::OpeningParenthesis => self.pattern_grouping(),
            _ => Err(ParseError::UnexpectedToken(
                self.tokens.next().unwrap().data,
            )),
        }
    }

    fn primary(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let Some(spanned_token) = self.tokens.peek() else {
            return Err(ParseError::UnexpectedEOF)
        };

        match &spanned_token.data {
            Token::Identifier(identifier) => {
                let expr = Expression::Identifier(identifier).attach(spanned_token.span);
                self.tokens.next();
                Ok(expr)
            }
            Token::Integer(integer) => {
                let expr = Expression::Integer(integer).attach(spanned_token.span);
                self.tokens.next();
                Ok(expr)
            }
            Token::Float(float) => {
                let expr = Expression::Float(float).attach(spanned_token.span);
                self.tokens.next();
                Ok(expr)
            }
            Token::String(string) => {
                let expr = Expression::String(string).attach(spanned_token.span);
                self.tokens.next();
                Ok(expr)
            }
            Token::OpeningParenthesis => self.grouping(),
            Token::KeywordLet => self.lett(),
            Token::Operator("\\") => self.lambda(),
            _ => Err(ParseError::UnexpectedToken(
                self.tokens.next().unwrap().data,
            )),
        }
    }

    fn application(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let mut expr = self.primary()?;

        while let Some(Token::OpeningParenthesis) = self.tokens.peek().map(|peeked| &peeked.data) {
            self.tokens.next();
            let mut args = vec![];
            if !self.peek_is(Token::ClosingParenthesis) {
                args.push(self.expression()?);
                while !self.peek_is(Token::ClosingParenthesis) {
                    self.expect(Token::Comma)?;
                    args.push(self.expression()?);
                }
            }
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

        while let Some(Token::Operator(lexeme)) = self.tokens.peek().map(|peeked| &peeked.data) {
            let (lexeme, assoc, op_precedence) =
                OPERATORS.iter().find(|(op, _, _)| op == lexeme).unwrap();

            if op_precedence < &min_precedence {
                break;
            }
            self.tokens.next();

            let rhs = self.binary(op_precedence + usize::from(assoc != &Associativity::Right))?;

            let span = lhs.span.extend(rhs.span);
            lhs = Expression::Binary {
                lhs: Box::new(lhs),
                op: lexeme,
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
type ParseResult<'a, T> = Result<T, ParseError<'a>>;

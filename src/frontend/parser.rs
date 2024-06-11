use std::iter::Peekable;

use crate::{backend::ast::Expression, frontend::token::Token};

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

    fn grouping(&mut self) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let start = self.expect(Token::OpeningParenthesis)?;
        let expr = self.expression()?;
        let end = self.expect(Token::ClosingParenthesis)?;

        Ok(Spanned::new(expr.data, start.extend(end)))
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
            _ => Err(ParseError::UnexpectedToken(
                self.tokens.next().unwrap().data,
            )),
        }
    }

    fn binary(
        &mut self,
        min_precedence: usize,
    ) -> ParseResult<'source, Spanned<'source, Expression<'source>>> {
        let mut lhs = self.primary()?;

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

pub enum ParseError<'source> {
    UnexpectedEOF,
    UnexpectedToken(Token<'source>),
}
type ParseResult<'a, T> = Result<T, ParseError<'a>>;

use std::{fmt::Display, fs::read_to_string, iter::Peekable};

use crate::{
    backend::ast::{
        Bound, Declaration, Expression, Namespace, Operator, Pattern, TypeExpr, TypedPattern
    },
    frontend::token::Token,
};

use super::{
    span::{HasSpan, Span, Spanned},
    token::Symbol,
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
    tokens: Peekable<Tokens<'source>>,
}

impl<'source> Parser<'source> {
    pub fn new(tokens: Tokens<'source>) -> Self {
        Self {
            tokens: tokens.peekable(),
        }
    }

    fn unexpected_eof<T>(&self) -> ParseResult<T> {
        Err(ParseError::UnexpectedEOF.attach(Span::eof()))
    }

    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        let Some(spanned_token) = self.tokens.next() else {
            return self.unexpected_eof()
        };

        (spanned_token.data == expected)
            .then_some(())
            .ok_or(ParseError::UnexpectedToken(spanned_token.data).attach(spanned_token.span))
    }

    fn expect_identifier(&mut self) -> ParseResult<Spanned<Symbol>> {
        let Some(spanned_token) = self.tokens.next() else {
            return self.unexpected_eof()
        };

        let Token::Identifier(identifier) = spanned_token.data else {
            return Err(ParseError::UnexpectedToken(spanned_token.data).attach(spanned_token.span))
        };

        Ok(Spanned::new(identifier, spanned_token.span))
    }

    fn next_peek_is(&mut self, expected: &Token) -> bool {
        self.tokens
            .next_if(|peeked| &peeked.data == expected)
            .is_some()
    }

    fn comma_seperated_until<T, F>(&mut self, f: F, until: Token) -> ParseResult<Vec<T>>
    where
        F: Fn(&mut Self) -> ParseResult<T>,
    {
        let mut things = vec![];
        if !self.next_peek_is(&until) {
            things.push(f(self)?);
            while !self.next_peek_is(&until) {
                self.expect(Token::Comma)?;
                things.push(f(self)?);
            }
        }

        Ok(things)
    }

    fn literal<T, F>(&mut self, constructor: F) -> ParseResult<T>
    where
        F: Fn(Spanned<Symbol>) -> T,
    {
        let token = self.tokens.next().unwrap();
        let symbol = token.data.to_string().into_boxed_str();
        Ok(constructor(Spanned::new(symbol, token.span)))
    }

    fn optional<T, F>(&mut self, f: F, condition_token: Token) -> ParseResult<Option<T>>
    where
        F: Fn(&mut Self) -> ParseResult<T>
    {
        Ok(if self.next_peek_is(&condition_token) {
            Some(f(self)?)
        } else {
            None
        })
    }

    fn grouping<T, F>(&mut self, f: F) -> ParseResult<T>
    where
        F: Fn(&mut Self) -> ParseResult<T>,
    {
        self.expect(Token::OpeningParenthesis)?;
        let expr = f(self)?;
        self.expect(Token::ClosingParenthesis)?;

        Ok(expr)
    }

    fn lett(&mut self) -> ParseResult<Expression> {
        self.expect(Token::KeywordLet)?;
        let pattern = self.pattern()?;
        let typ = self.optional(Self::type_expr, Token::Colon)?;
        self.expect(Token::Equals)?;
        let expr = Box::new(self.expression()?);
        self.expect(Token::KeywordIn)?;
        let body = Box::new(self.expression()?);

        Ok(Expression::Let {
            pattern,
            typ,
            expr,
            body,
        })
    }

    fn lambda(&mut self) -> ParseResult<Expression> {
        self.expect(Token::Backslash)?;
        let params = self.comma_seperated_until(Self::pattern, Token::RightArrow)?;
        let body = Box::new(self.expression()?);

        Ok(Expression::Lambda { params, body })
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::Identifier(_) => self.literal(Pattern::Any),
            Token::Integer(_) => self.literal(Pattern::Integer),
            Token::Float(_) => self.literal(Pattern::Float),
            Token::String(_) => self.literal(Pattern::String),
            Token::OpeningParenthesis => self.grouping(Self::pattern),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    fn identifier(&mut self) -> ParseResult<Expression> {
        let identifier = self.expect_identifier()?;
        Ok(if self.next_peek_is(&Token::DoubleColon) {
            Expression::Access {
                from: identifier,
                name: self.expect_identifier()?,
                namespace: Namespace::Undetermined,
            }
        } else {
            Expression::Identifier(identifier, Bound::None)
        })
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::Identifier(_) => self.identifier(),
            Token::Integer(_) => self.literal(Expression::Integer),
            Token::Float(_) => self.literal(Expression::Float),
            Token::String(_) => self.literal(Expression::String),
            Token::KeywordNothing => Ok(Expression::Nothing(self.tokens.next().unwrap().span)),
            Token::OpeningParenthesis => self.grouping(Self::expression),
            Token::KeywordLet => self.lett(),
            Token::Backslash => self.lambda(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    fn application(&mut self) -> ParseResult<Expression> {
        let mut expr = self.primary()?;

        while self.next_peek_is(&Token::OpeningParenthesis) {
            expr = Expression::Application {
                expr: Box::new(expr),
                args: self.comma_seperated_until(Self::expression, Token::ClosingParenthesis)?,
            };
        }

        Ok(expr)
    }

    fn binary(&mut self, min_precedence: usize) -> ParseResult<Expression> {
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

            lhs = Expression::Binary {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            };

            if assoc == &Associativity::None {
                break;
            }
        }

        Ok(lhs)
    }

    pub fn expression(&mut self) -> ParseResult<Expression> {
        self.binary(0)
    }

    fn func_type(&mut self) -> ParseResult<TypeExpr> {
        self.expect(Token::KeywordFunc)?;
        self.expect(Token::OpeningParenthesis)?;
        let params = self.comma_seperated_until(Self::type_expr, Token::ClosingParenthesis)?;
        self.expect(Token::RightArrow)?;
        let ret = Box::new(self.type_expr()?);

        Ok(TypeExpr::Function { params, ret })
    }

    fn type_expr(&mut self) -> ParseResult<TypeExpr> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::Identifier(_) => {
                let token = self.tokens.next().unwrap();
                let symbol = token.data.to_string().into_boxed_str();
                Ok(TypeExpr::Identifier(
                    Spanned::new(symbol, token.span),
                    Bound::None,
                ))
            }
            Token::OpeningParenthesis => self.grouping(Self::type_expr),
            Token::KeywordFunc => self.func_type(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    fn typed_pattern(&mut self) -> ParseResult<TypedPattern> {
        let pattern = self.pattern()?;
        self.expect(Token::Colon)?;
        let typ = self.type_expr()?;

        Ok(TypedPattern { pattern, typ })
    }

    fn func(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordFunc)?;
        let name = self.expect_identifier()?;
        self.expect(Token::OpeningParenthesis)?;
        let params = self.comma_seperated_until(Self::typed_pattern, Token::ClosingParenthesis)?;
        let ret = self.optional(Self::type_expr, Token::RightArrow)?;
        self.expect(Token::Equals)?;
        let body = self.expression()?;

        Ok(Declaration::Function { name, params, body, ret })
    }

    fn import(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordImport)?;
        let mut parts = vec![self.expect_identifier()?];
        while self.next_peek_is(&Token::DoubleColon) {
            parts.push(self.expect_identifier()?);
        }

        // TODO: Do not hardcode the file extension.
        let import_path = parts.iter().fold(String::from("."), |mut acc, part| {
            acc.push('\\');
            acc.push_str(&part.data);
            acc
        }) + ".txt";

        // TODO: Remove unwrap.
        let import_file = read_to_string(&import_path).unwrap();
        let import =
            Parser::new(Tokens::new(&import_file))
                .declarations()
                .map_err(|error| {
                    let first = parts.first().unwrap().span;
                    let last = parts.last().unwrap().span;
                    let span = first.extend(last);
                    ParseError::ImportError {
                        import_path: import_path.clone().into(),
                        error: Box::new(error),
                    }
                    .attach(span)
                })?;

        Ok(Declaration::Import { parts, import })
    }

    fn type_constructor(&mut self) -> ParseResult<(Spanned<Symbol>, Vec<TypeExpr>)> {
        let name = self.expect_identifier()?;
        let params = if self.next_peek_is(&Token::OpeningParenthesis) {
            self.comma_seperated_until(Self::type_expr, Token::ClosingParenthesis)?
        } else {
            vec![]
        };

        Ok((name, params))
    }

    fn typee(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordType)?;
        let name = self.expect_identifier()?;
        self.expect(Token::Equals)?;
        let mut consts = vec![self.type_constructor()?];
        while self.next_peek_is(&Token::Bar) {
            consts.push(self.type_constructor()?);
        }

        Ok(Declaration::Type { name, consts })
    }

    fn declaration(&mut self) -> ParseResult<Declaration> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::KeywordFunc => self.func(),
            Token::KeywordImport => self.import(),
            Token::KeywordType => self.typee(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    pub fn declarations(&mut self) -> ParseResult<Vec<Declaration>> {
        let mut declarations = vec![];
        while self.tokens.peek().is_some() {
            declarations.push(self.declaration()?)
        }

        Ok(declarations)
    }
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedEOF,
    UnexpectedToken(Token),
    ImportError {
        import_path: Symbol,
        error: Box<Spanned<ParseError>>,
    },
}

impl HasSpan for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEOF => write!(f, "Unexpected EOF."),
            Self::UnexpectedToken(unexpected) => write!(f, "Unexpected token: `{unexpected}`."),
            Self::ImportError { .. } => write!(f, "Error while importing module."),
        }
    }
}

type ParseResult<T> = Result<T, Spanned<ParseError>>;

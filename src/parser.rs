use core::fmt;
use std::{iter::Peekable, result};

use crate::{
    error,
    ranged::Ranged,
    tokens::{Token, TokenError, Tokens},
};

#[rustfmt::skip]
const BINARY_OPERATORS: [(Token, Associativity, usize); 14] = [
    (Token::OrKeyword,     Associativity::Left,  0),
    (Token::AndKeyword,    Associativity::Left,  1),
    (Token::DoubleEquals,  Associativity::None,  2),
    (Token::SlashEquals,   Associativity::None,  2),
    (Token::Less,          Associativity::None,  3),
    (Token::LessEquals,    Associativity::None,  3),
    (Token::Greater,       Associativity::None,  3),
    (Token::GreaterEquals, Associativity::None,  3),
    (Token::Colon,         Associativity::Right, 4),
    (Token::Plus,          Associativity::Left,  5),
    (Token::Minus,         Associativity::Left,  5),
    (Token::Asterisk,      Associativity::Left,  6),
    (Token::Slash,         Associativity::Left,  6),
    (Token::ModKeyword,    Associativity::Left,  6),
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

    fn peek_token(&mut self) -> ParseResult<&Token> {
        Ok(self
            .tokens
            .peek()
            .map(result::Result::as_ref)
            .ok_or_else(|| Ranged::new(ParseError::UnexpectedEOF, Default::default()))?
            .map(Ranged::as_ref)?)
    }

    fn next_token(&mut self) -> ParseResult<Token> {
        Ok(self
            .tokens
            .next()
            .ok_or_else(|| Ranged::new(ParseError::UnexpectedEOF, Default::default()))??)
    }

    #[allow(clippy::needless_pass_by_value)]
    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        let (token, ranges) = self.next_token()?.into_tuple();
        if token == expected {
            Ok(Ranged::new((), ranges))
        } else {
            Err(Ranged::new(ParseError::UnexpectedToken(token), ranges))
        }
    }

    fn expect_ident(&mut self) -> ParseResult<String> {
        let (token, ranges) = self.next_token()?.into_tuple();
        if let Token::Identifier(name) = token {
            Ok(Ranged::new(name, ranges))
        } else {
            Err(Ranged::new(ParseError::UnexpectedToken(token), ranges))
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn optional(&mut self, optional: Token) -> bool {
        self.peek_token()
            .map(|token| token.data)
            .map_or(false, |token| token == &optional)
    }

    fn parse_pattern_grouping(&mut self) -> ParseResult<Pattern> {
        let starts = self.expect(Token::OpeningParenthesis).unwrap().starts();
        Ok(if self.optional(Token::ClosingParenthesis) {
            let ends = self.expect(Token::ClosingParenthesis).unwrap().ends();
            Ranged::new(Pattern::Unit, (starts, ends))
        } else {
            let pattern = self.pattern()?.data;
            let ends = self.expect(Token::ClosingParenthesis)?.ends();
            Ranged::new(pattern, (starts, ends))
        })
    }

    fn parse_negative_number_pattern(&mut self) -> ParseResult<Pattern> {
        let starts = self.expect(Token::Minus).unwrap().starts();
        let (token, ranges) = self.next_token()?.into_tuple();
        match token {
            Token::NaturalNumber(nat) => Ok(Ranged::new(
                Pattern::NegativeInteger(nat),
                (starts, ranges.1),
            )),
            unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
        }
    }

    fn primary_pattern(&mut self) -> ParseResult<Pattern> {
        match self.peek_token()?.data {
            Token::OpeningParenthesis => self.parse_pattern_grouping(),
            Token::Minus => self.parse_negative_number_pattern(),
            _ => {
                let (token, ranges) = self.tokens.next().unwrap().unwrap().into_tuple();
                match token {
                    Token::Identifier(ident) => Ok(Ranged::new(Pattern::All(ident), ranges)),
                    Token::NaturalNumber(nat) => {
                        Ok(Ranged::new(Pattern::NaturalNumber(nat), ranges))
                    }
                    Token::TrueKeyword => Ok(Ranged::new(Pattern::Boolean(true), ranges)),
                    Token::FalseKeyword => Ok(Ranged::new(Pattern::Boolean(false), ranges)),
                    unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
                }
            }
        }
    }

    fn pair_pattern(&mut self) -> ParseResult<Pattern> {
        let primary = self.primary_pattern()?;

        if self.optional(Token::Colon) {
            self.tokens.next();
            let second = self.pair_pattern()?;
            let starts = primary.starts();
            let ends = second.ends();
            Ok(Ranged::new(
                Pattern::Pair {
                    first: Box::new(primary),
                    second: Box::new(second),
                },
                (starts, ends),
            ))
        } else {
            Ok(primary)
        }
    }

    fn or_pattern(&mut self) -> ParseResult<Pattern> {
        let mut pattern = self.pair_pattern()?;

        while self.optional(Token::Comma) {
            self.tokens.next();
            let left = self.pair_pattern()?;
            let starts = pattern.starts();
            let ends = left.ends();
            pattern = Ranged::new(
                Pattern::Or {
                    right: Box::new(pattern),
                    left: Box::new(left),
                },
                (starts, ends),
            );
        }

        Ok(pattern)
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        self.or_pattern()
    }

    fn parse_grouping(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::OpeningParenthesis).unwrap().starts();
        Ok(if self.optional(Token::ClosingParenthesis) {
            let ends = self.expect(Token::ClosingParenthesis).unwrap().ends();
            Ranged::new(Expression::Unit, (starts, ends))
        } else {
            let expr = self.expression()?.data;
            let ends = self.expect(Token::ClosingParenthesis)?.ends();
            Ranged::new(expr, (starts, ends))
        })
    }

    fn parse_let(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::LetKeyword).unwrap().starts();
        let pattern = self.pattern()?;
        self.expect(Token::Equals)?;
        let value_expr = Box::new(self.expression()?);
        self.expect(Token::InKeyword)?;
        let return_expr = Box::new(self.expression()?);
        let ends = return_expr.ends();

        Ok(Ranged::new(
            Expression::Let {
                pattern,
                value_expr,
                return_expr,
            },
            (starts, ends),
        ))
    }

    fn parse_lambda(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::Backslash).unwrap().starts();
        let mut args = vec![];
        if !self.optional(Token::Arrow) {
            args.push(self.pattern()?);
            while !self.optional(Token::Arrow) {
                self.expect(Token::Comma)?;
                args.push(self.pattern()?);
            }
        }
        self.expect(Token::Arrow)?;
        let expr = Box::new(self.expression()?);
        let ends = expr.ends();

        Ok(Ranged::new(
            Expression::Function { args, expr },
            (starts, ends),
        ))
    }

    fn parse_import(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::ImportKeyword).unwrap().starts();
        let part = self.expect_ident()?;
        let mut ends = part.ends();
        let mut parts = vec![part.data];
        while self.optional(Token::Dot) {
            self.tokens.next();
            let part = self.expect_ident()?;
            ends = part.ends();
            parts.push(part.data);
        }

        Ok(Ranged::new(Expression::Import(parts), (starts, ends)))
    }

    fn parse_match(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::MatchKeyword).unwrap().starts();
        let expr = Box::new(self.expression()?);

        self.expect(Token::Bar)?;
        let pattern = self.pattern()?;
        self.expect(Token::Arrow)?;
        let branch_expr = Box::new(self.expression()?);
        let mut ends = branch_expr.ends();

        let mut branches = vec![(pattern, branch_expr)];
        while self.optional(Token::Bar) {
            self.tokens.next();
            let pattern = self.pattern()?;
            self.expect(Token::Arrow)?;
            let expr = Box::new(self.expression()?);
            ends = expr.ends();
            branches.push((pattern, expr));
        }

        Ok(Ranged::new(
            Expression::Match { expr, branches },
            (starts, ends),
        ))
    }

    fn parse_negation(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::Minus).unwrap().starts();
        let expr = Box::new(self.primary()?);
        let ends = expr.ends();

        Ok(Ranged::new(Expression::Negation(expr), (starts, ends)))
    }

    fn parse_if(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::IfKeyword).unwrap().starts();
        let cond = Box::new(self.expression()?);
        self.expect(Token::ThenKeyword)?;
        let then = Box::new(self.expression()?);
        self.expect(Token::ElseKeyword)?;
        let otherwise = Box::new(self.expression()?);
        let ends = otherwise.ends();

        Ok(Ranged::new(
            Expression::If {
                cond,
                then,
                otherwise,
            },
            (starts, ends),
        ))
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        match self.peek_token()?.data {
            Token::OpeningParenthesis => self.parse_grouping(),
            Token::LetKeyword => self.parse_let(),
            Token::Backslash => self.parse_lambda(),
            Token::ImportKeyword => self.parse_import(),
            Token::MatchKeyword => self.parse_match(),
            Token::Minus => self.parse_negation(),
            Token::IfKeyword => self.parse_if(),
            _ => {
                let (token, ranges) = self.tokens.next().unwrap().unwrap().into_tuple();
                match token {
                    Token::Identifier(ident) => {
                        Ok(Ranged::new(Expression::Identifier(ident), ranges))
                    }
                    Token::NaturalNumber(nat) => {
                        Ok(Ranged::new(Expression::NaturalNumber(nat), ranges))
                    }
                    Token::TrueKeyword => Ok(Ranged::new(Expression::Boolean(true), ranges)),
                    Token::FalseKeyword => Ok(Ranged::new(Expression::Boolean(false), ranges)),
                    unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
                }
            }
        }
    }

    fn application_and_access(&mut self) -> ParseResult<Expression> {
        let mut expr = self.primary()?;

        while let Some(token_result) = self.tokens.peek() {
            match &token_result.as_ref()?.data {
                Token::OpeningParenthesis => {
                    self.tokens.next();
                    let mut args = vec![];
                    if !self.optional(Token::ClosingParenthesis) {
                        args.push(self.expression()?);
                        while !self.optional(Token::ClosingParenthesis) {
                            self.expect(Token::Comma)?;
                            args.push(self.expression()?);
                        }
                    }
                    let starts = expr.starts();
                    let ends = self.expect(Token::ClosingParenthesis)?.ends();

                    expr = Ranged::new(
                        Expression::Application {
                            expr: Box::new(expr),
                            args,
                        },
                        (starts, ends),
                    );
                }
                Token::Dot => {
                    self.tokens.next();
                    let what = self.expect_ident()?;
                    let starts = expr.starts();
                    let ends = what.ends();
                    expr = Ranged::new(
                        Expression::Access {
                            from: Box::new(expr),
                            what,
                        },
                        (starts, ends),
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn binary(&mut self, min_prec: usize) -> ParseResult<Expression> {
        let mut expr = self.application_and_access()?;

        while let Some(token_result) = self.tokens.peek() {
            let token = &token_result.as_ref()?.data;

            let Some((op_token, assoc, prec)) = BINARY_OPERATORS.iter().find(|(op_token, _, _)| op_token == token) else {
                break;
            };

            if prec < &min_prec {
                break;
            }

            let bop = op_token.into();
            let prec = *prec;

            self.tokens.next();
            let rhs = self.binary(prec + usize::from(assoc != &Associativity::Right))?;

            let starts = expr.starts();
            let ends = rhs.ends();
            expr = Ranged::new(
                Expression::Binary {
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                    bop,
                },
                (starts, ends),
            );

            if assoc == &Associativity::None {
                break;
            }
        }

        Ok(expr)
    }

    fn expression(&mut self) -> ParseResult<Expression> {
        self.binary(0)
    }

    pub fn parse_expr(&mut self) -> ParseResult<Expression> {
        let (expr, ranges) = self.expression()?.into_tuple();

        match self.tokens.next() {
            Some(token_result) => Err(Ranged::new(ParseError::Unconsumed, token_result?.ranges())),
            None => Ok(Ranged::new(expr, ranges)),
        }
    }

    pub fn parse_module(
        &mut self,
    ) -> Result<Vec<(String, Ranged<Expression>)>, Ranged<ParseError>> {
        let mut definitions = vec![];
        while self.tokens.peek().is_some() {
            let name = self.expect_ident()?.data;
            self.expect(Token::Equals)?;
            definitions.push((name, self.expression()?));
        }

        Ok(definitions)
    }
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedEOF,
    TokenError(TokenError),
    UnexpectedToken(Token),
    Unconsumed,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEOF => write!(f, "Unexpectedly encountered EOF while parsing."),
            Self::TokenError(error) => write!(f, "{error}"),
            Self::UnexpectedToken(token) => write!(f, "`{token:?}` was not expected."),
            Self::Unconsumed => write!(f, "From here, the rest couldn't be consumed."),
        }
    }
}

impl From<Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: Ranged<TokenError>) -> Self {
        let ranges = value.ranges();
        Self::new(ParseError::TokenError(value.data), ranges)
    }
}

impl From<&Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: &Ranged<TokenError>) -> Self {
        Self::new(ParseError::TokenError(value.data.clone()), value.ranges())
    }
}

impl Ranged<ParseError> {
    pub fn report(&self, source_name: &str, source: &str) {
        if matches!(self.data, ParseError::UnexpectedEOF) {
            error::report_unexpected_eof(&self.data, source_name, source);
        } else {
            error::report(self, source_name, source, "parsing");
        }
    }
}

type ParseResult<T> = Result<Ranged<T>, Ranged<ParseError>>;

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(String),
    NaturalNumber(String),
    Binary {
        lhs: Box<Ranged<Expression>>,
        rhs: Box<Ranged<Expression>>,
        bop: BinaryOp,
    },
    Let {
        pattern: Ranged<Pattern>,
        value_expr: Box<Ranged<Expression>>,
        return_expr: Box<Ranged<Expression>>,
    },
    Function {
        args: Vec<Ranged<Pattern>>,
        expr: Box<Ranged<Expression>>,
    },
    Application {
        expr: Box<Ranged<Expression>>,
        args: Vec<Ranged<Expression>>,
    },
    Access {
        from: Box<Ranged<Expression>>,
        what: Ranged<String>,
    },
    Import(Vec<String>),
    Match {
        expr: Box<Ranged<Expression>>,
        branches: Vec<(Ranged<Pattern>, Box<Ranged<Expression>>)>,
    },
    Boolean(bool),
    Unit,
    Negation(Box<Ranged<Expression>>),
    If {
        cond: Box<Ranged<Expression>>,
        then: Box<Ranged<Expression>>,
        otherwise: Box<Ranged<Expression>>,
    },
}

#[derive(Clone, Debug)]
pub enum Pattern {
    All(String),
    NaturalNumber(String),
    Pair {
        first: Box<Ranged<Pattern>>,
        second: Box<Ranged<Pattern>>,
    },
    Or {
        right: Box<Ranged<Pattern>>,
        left: Box<Ranged<Pattern>>,
    },
    Boolean(bool),
    Unit,
    NegativeInteger(String),
}

#[derive(Clone, Copy, Debug)]
pub enum BinaryOp {
    Addition,
    Subtraction,
    Multiplication,
    Division,
    Modulo,
    Pairing,
    Equivalence,
    NonEquivalence,
    BooleanOr,
    BooleanAnd,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
}

impl std::fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Addition => write!(f, "+"),
            Self::Subtraction => write!(f, "-"),
            Self::Multiplication => write!(f, "*"),
            Self::Division => write!(f, "/"),
            Self::Modulo => write!(f, "mod"),
            Self::Pairing => write!(f, ":"),
            Self::Equivalence => write!(f, "=="),
            Self::NonEquivalence => write!(f, "/="),
            Self::BooleanOr => write!(f, "or"),
            Self::BooleanAnd => write!(f, "and"),
            Self::Less => write!(f, "<"),
            Self::LessOrEqual => write!(f, "<="),
            Self::Greater => write!(f, ">"),
            Self::GreaterOrEqual => write!(f, ">="),
        }
    }
}

impl From<&Token> for BinaryOp {
    fn from(val: &Token) -> Self {
        match val {
            Token::Asterisk => Self::Multiplication,
            Token::Slash => Self::Division,
            Token::ModKeyword => Self::Modulo,
            Token::Minus => Self::Subtraction,
            Token::Plus => Self::Addition,
            Token::Colon => Self::Pairing,
            Token::DoubleEquals => Self::Equivalence,
            Token::SlashEquals => Self::NonEquivalence,
            Token::OrKeyword => Self::BooleanOr,
            Token::AndKeyword => Self::BooleanAnd,
            Token::Less => Self::Less,
            Token::LessEquals => Self::LessOrEqual,
            Token::Greater => Self::Greater,
            Token::GreaterEquals => Self::GreaterOrEqual,
            _ => unreachable!(),
        }
    }
}

#[derive(PartialEq)]
enum Associativity {
    Right,
    Left,
    None,
}

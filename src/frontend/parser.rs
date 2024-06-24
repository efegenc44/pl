use std::{collections::HashMap, fmt::Display, fs::read_to_string, iter::Peekable};

use crate::{
    backend::ast::{Bound, Declaration, Expression, Module, Operator, Pattern},
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
    imports: HashMap<Symbol, Module>,
}

impl<'source> Parser<'source> {
    pub fn new(tokens: Tokens<'source>) -> Self {
        Self {
            tokens: tokens.peekable(),
            imports: HashMap::new(),
        }
    }

    fn unexpected_eof<T>(&self) -> ParseResult<T> {
        Err(ParseError::UnexpectedEOF.attach(Span::eof()))
    }

    fn expect(&mut self, expected: Token) -> ParseResult<Span> {
        let Some(spanned_token) = self.tokens.next() else {
            return self.unexpected_eof()
        };

        if spanned_token.data == expected {
            Ok(spanned_token.span)
        } else {
            Err(ParseError::UnexpectedToken(spanned_token.data).attach(spanned_token.span))
        }
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

    fn peek_is(&mut self, expected: &Token) -> bool {
        self.tokens
            .peek()
            .map_or(false, |peeked| &peeked.data == expected)
    }

    fn comma_seperated_until<T, F>(&mut self, f: F, until: Token) -> ParseResult<Vec<T>>
    where
        F: Fn(&mut Self) -> ParseResult<T>,
    {
        let mut things = vec![];
        if !self.peek_is(&until) {
            things.push(f(self)?);
            while !self.peek_is(&until) {
                self.expect(Token::Comma)?;
                things.push(f(self)?);
            }
        }

        Ok(things)
    }

    fn literal<T, F>(&mut self, constructor: F, span: Span) -> ParseResult<Spanned<T>>
    where
        T: HasSpan,
        F: Fn(Symbol) -> T,
    {
        let token = self.tokens.next().unwrap();
        Ok(constructor(token.to_string().into_boxed_str()).attach(span))
    }

    fn grouping(&mut self) -> ParseResult<Spanned<Expression>> {
        let start = self.expect(Token::OpeningParenthesis)?;
        let expr = self.expression()?;
        let end = self.expect(Token::ClosingParenthesis)?;

        Ok(expr.data.attach(start.extend(end)))
    }

    fn pattern_grouping(&mut self) -> ParseResult<Spanned<Pattern>> {
        let start = self.expect(Token::OpeningParenthesis)?;
        let expr = self.pattern()?;
        let end = self.expect(Token::ClosingParenthesis)?;

        Ok(expr.data.attach(start.extend(end)))
    }

    fn lett(&mut self) -> ParseResult<Spanned<Expression>> {
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

    fn lambda(&mut self) -> ParseResult<Spanned<Expression>> {
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

    fn pattern(&mut self) -> ParseResult<Spanned<Pattern>> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        let span = peeked.span;
        match &peeked.data {
            Token::Identifier(_) => self.literal(Pattern::Any, span),
            Token::Integer(_) => self.literal(Pattern::Integer, span),
            Token::Float(_) => self.literal(Pattern::Float, span),
            Token::String(_) => self.literal(Pattern::String, span),
            Token::OpeningParenthesis => self.pattern_grouping(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(span)),
        }
    }

    fn primary(&mut self) -> ParseResult<Spanned<Expression>> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        let span = peeked.span;
        match &peeked.data {
            Token::Identifier(_) => {
                let identifier = self.tokens.next().unwrap().to_string().into_boxed_str();
                let expr = if let Some(Token::Dot) = self.tokens.peek().map(|peeked| &peeked.data) {
                    self.tokens.next();
                    let name = self.expect_identifier()?;
                    let end = name.span;

                    Expression::Access {
                        module_name: Spanned::new(identifier, span),
                        name,
                    }
                    .attach(span.extend(end))
                } else {
                    Expression::Identifier(identifier, Bound::None).attach(span)
                };

                Ok(expr)
            }
            Token::Integer(_) => self.literal(Expression::Integer, span),
            Token::Float(_) => self.literal(Expression::Float, span),
            Token::String(_) => self.literal(Expression::String, span),
            Token::OpeningParenthesis => self.grouping(),
            Token::KeywordLet => self.lett(),
            Token::Backslash => self.lambda(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(span)),
        }
    }

    fn application(&mut self) -> ParseResult<Spanned<Expression>> {
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

    fn binary(&mut self, min_precedence: usize) -> ParseResult<Spanned<Expression>> {
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

    pub fn expression(&mut self) -> ParseResult<Spanned<Expression>> {
        self.binary(0)
    }

    fn func(&mut self) -> ParseResult<Spanned<Declaration>> {
        let start = self.expect(Token::KeywordFunc)?;
        let name = self.expect_identifier()?;
        self.expect(Token::OpeningParenthesis)?;
        let params = self.comma_seperated_until(Self::pattern, Token::ClosingParenthesis)?;
        self.expect(Token::ClosingParenthesis)?;
        self.expect(Token::Equals)?;
        let body = self.expression()?;
        let end = body.span;

        Ok(Declaration::Function { name, params, body }.attach(start.extend(end)))
    }

    fn import(&mut self) -> ParseResult<Spanned<Declaration>> {
        let start = self.expect(Token::KeywordImport)?;
        let mut parts = vec![];
        parts.push(self.expect_identifier()?);
        while self
            .tokens
            .next_if(|next| next.data == Token::Dot)
            .is_some()
        {
            parts.push(self.expect_identifier()?);
        }
        let module_name = parts.last().unwrap().data.clone();
        let end = parts.last().unwrap().span;

        let module_path = String::from(".")
            + &parts
                .iter()
                .map(|part| &part.data)
                .fold(String::new(), |x, y| x + "\\" + y.as_ref())
            + ".txt";

        // TODO: Remove unwrap.
        let module_file = read_to_string(&module_path).unwrap();
        let module = Parser::new(Tokens::new(&module_file))
            .module()
            .map_err(|err| {
                ParseError::ImportError {
                    import_path: module_path.into(),
                    error: Box::new(err),
                }
                .attach(start.extend(end))
            })?;

        self.imports.insert(module_name, module);

        Ok(Declaration::Import { parts }.attach(start.extend(end)))
    }

    fn declaration(&mut self) -> ParseResult<Spanned<Declaration>> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        let span = peeked.span;
        match &peeked.data {
            Token::KeywordFunc => self.func(),
            Token::KeywordImport => self.import(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(span)),
        }
    }

    pub fn module(mut self) -> Result<Module, Spanned<ParseError>> {
        let mut module = HashMap::new();
        while self.tokens.peek().is_some() {
            let decl = self.declaration()?;
            match &decl.data {
                Declaration::Function { name, .. } => {
                    module.insert(name.data.clone(), decl);
                }
                Declaration::Import { .. } => (),
            };
        }

        Ok(Module::new(module, self.imports))
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

impl ParseError {
    fn attach(self, span: Span) -> Spanned<Self> {
        Spanned::new(self, span)
    }
}

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

use std::{collections::HashMap, fmt::Display, fs::read_to_string, iter::Peekable};

use crate::{
    backend::ast::{Bound, Declaration, Expression, Import, Module, Operator, Pattern},
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
        self.expect(Token::Equals)?;
        let expr = Box::new(self.expression()?);
        self.expect(Token::KeywordIn)?;
        let body = Box::new(self.expression()?);

        Ok(Expression::Let {
            pattern,
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
                module_name: identifier,
                name: self.expect_identifier()?,
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

    fn func(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordFunc)?;
        let name = self.expect_identifier()?;
        self.expect(Token::OpeningParenthesis)?;
        let params = self.comma_seperated_until(Self::pattern, Token::ClosingParenthesis)?;
        self.expect(Token::Equals)?;
        let body = self.expression()?;

        Ok(Declaration::Function { name, params, body })
    }

    fn import(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordImport)?;
        let mut parts = vec![self.expect_identifier()?];
        while self.next_peek_is(&Token::DoubleColon) {
            parts.push(self.expect_identifier()?);
        }

        Ok(Declaration::Import { parts })
    }

    fn declaration(&mut self) -> ParseResult<Declaration> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::KeywordFunc => self.func(),
            Token::KeywordImport => self.import(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    pub fn module(mut self) -> ParseResult<Module> {
        let mut decls = HashMap::new();
        let mut imports = HashMap::new();
        while self.tokens.peek().is_some() {
            let decl = self.declaration()?;
            match decl {
                Declaration::Function { ref name, .. } => {
                    // TODO
                    let span = name.span;
                    let name = name.data.clone();
                    if decls.insert(name.clone(), decl).is_some() {
                        return Err(ParseError::DuplicateDeclaration(name).attach(span))
                    }
                },
                Declaration::Import { parts, .. } => {
                    // TODO: Do not hardcode the file extension.
                    let import_path = parts.iter().fold(String::from("."), |mut acc, part| {
                        acc.push('\\');
                        acc.push_str(&part.data);
                        acc
                    }) + ".txt";

                    let first = parts.first().unwrap().span;
                    let last = parts.last().unwrap().span;
                    let span = first.extend(last);

                    // TODO: Remove unwrap.
                    let module_file = read_to_string(&import_path).unwrap();
                    let module = Parser::new(Tokens::new(&module_file))
                        .module()
                        .map_err(|error| {
                            ParseError::ImportError {
                                import_path: import_path.clone().into(),
                                error: Box::new(error),
                            }
                            .attach(span)
                        })?;

                    let module_name = parts.last().unwrap().data.clone();
                    imports.insert(module_name, Import::new(span, import_path.into(), module));
                },
            };
        }

        Ok(Module::new(decls, imports))
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
    DuplicateDeclaration(Symbol),
}

impl HasSpan for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEOF => write!(f, "Unexpected EOF."),
            Self::UnexpectedToken(unexpected) => write!(f, "Unexpected token: `{unexpected}`."),
            Self::ImportError { .. } => write!(f, "Error while importing module."),
            Self::DuplicateDeclaration(identifier) => write!(f, "`{identifier}` has already declared."),
        }
    }
}

type ParseResult<T> = Result<T, Spanned<ParseError>>;

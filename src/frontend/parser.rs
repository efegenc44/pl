use std::{fmt::Display, fs::{read_dir, read_to_string}, iter::Peekable, path::PathBuf};

use crate::{
    backend::ast::{
        Access, Application, Bound, Declaration, Expression, TypeFunction, ImportKind, Let, Namespace, Pattern, TypeExpression
    },
    frontend::token::Token,
};

use super::{
    span::{HasSpan, Span, Spanned},
    token::Symbol,
    tokens::Tokens,
};

pub struct Parser<'source> {
    file_path: PathBuf,
    tokens: Peekable<Tokens<'source>>,
}

impl<'source> Parser<'source> {
    pub fn new(tokens: Tokens<'source>, mut file_path: PathBuf) -> Self {
        file_path.pop();

        Self {
            tokens: tokens.peekable(),
            file_path,
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
        let expr = Box::new(self.expression()?);
        let type_expr = self.optional(Self::type_expr, Token::Colon)?;
        self.expect(Token::Equals)?;
        let mut branches = vec![self.let_branch()?];
        while self.next_peek_is(&Token::Bar) {
            branches.push(self.let_branch()?);
        }

        Ok(Expression::Let(Let {
            type_expr,
            expr,
            branches,
        }))
    }

    fn let_branch(&mut self) -> ParseResult<(Pattern, Box<Expression>)> {
        let pattern = self.pattern()?;
        self.expect(Token::RightArrow)?;
        let expr = Box::new(self.expression()?);

        Ok((pattern, expr))
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::Identifier(_) => self.pattern_identifier(),
            Token::Integer(_) => self.literal(Pattern::Integer),
            Token::Float(_) => self.literal(Pattern::Float),
            Token::String(_) => self.literal(Pattern::String),
            Token::OpeningParenthesis => self.grouping(Self::pattern),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    fn pattern_identifier(&mut self) -> ParseResult<Pattern> {
        let identifier = self.expect_identifier()?;
        if self.next_peek_is(&Token::DoubleColon) {
            let mut path = vec![identifier, self.expect_identifier()?];
            while self.next_peek_is(&Token::DoubleColon) {
                path.push(self.expect_identifier()?);
            }

            let params = if self.next_peek_is(&Token::OpeningParenthesis) {
                self.comma_seperated_until(Self::pattern, Token::ClosingParenthesis)?
            } else {
                vec![]
            };

            Ok(Pattern::Constructor { path, params, real_path: vec![] })
        } else if self.next_peek_is(&Token::OpeningParenthesis) {
            let params = self.comma_seperated_until(Self::pattern, Token::ClosingParenthesis)?;
            Ok(Pattern::Constructor { path: vec![identifier], params, real_path: vec![] })
        } else {
            Ok(Pattern::Any(Spanned::new(identifier.data, identifier.span)))
        }
    }

    fn identifier(&mut self) -> ParseResult<Expression> {
        let identifier = self.expect_identifier()?;
        Ok(if self.next_peek_is(&Token::DoubleColon) {
            let mut path = vec![identifier, self.expect_identifier()?];
            while self.next_peek_is(&Token::DoubleColon) {
                path.push(self.expect_identifier()?);
            }

            Expression::Access(Access {
                path,
                namespace: Namespace::Undetermined,
                real_path: Vec::new(),
            })
        } else {
            Expression::Identifier(identifier, Bound::None)
        })
    }

    fn type_identifier(&mut self) -> ParseResult<TypeExpression> {
        let identifier = self.expect_identifier()?;
        Ok(if self.next_peek_is(&Token::DoubleColon) {
            let mut path = vec![identifier, self.expect_identifier()?];
            while self.next_peek_is(&Token::DoubleColon) {
                path.push(self.expect_identifier()?);
            }

            TypeExpression::Access(path, vec![])
        } else {
            TypeExpression::Identifier(identifier, Bound::None)
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
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    fn application(&mut self) -> ParseResult<Expression> {
        let mut expr = self.primary()?;

        while self.next_peek_is(&Token::OpeningParenthesis) {
            expr = Expression::Application(Application {
                expr: Box::new(expr),
                args: self.comma_seperated_until(Self::expression, Token::ClosingParenthesis)?,
            });
        }

        Ok(expr)
    }

    pub fn expression(&mut self) -> ParseResult<Expression> {
        self.application()
    }

    fn func_type(&mut self) -> ParseResult<TypeExpression> {
        self.expect(Token::KeywordFunc)?;
        self.expect(Token::OpeningParenthesis)?;
        let params = self.comma_seperated_until(Self::type_expr, Token::ClosingParenthesis)?;
        self.expect(Token::RightArrow)?;
        let ret = Box::new(self.type_expr()?);

        Ok(TypeExpression::Function(TypeFunction { params, ret }))
    }

    fn type_expr(&mut self) -> ParseResult<TypeExpression> {
        let Some(peeked) = self.tokens.peek() else {
            return self.unexpected_eof()
        };

        match &peeked.data {
            Token::Identifier(_) => self.type_identifier(),
            Token::OpeningParenthesis => self.grouping(Self::type_expr),
            Token::KeywordFunc => self.func_type(),
            unexpected => Err(ParseError::UnexpectedToken(unexpected.clone()).attach(peeked.span)),
        }
    }

    fn func(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordFunc)?;
        let name = self.expect_identifier()?;
        self.expect(Token::OpeningParenthesis)?;
        let params = self.comma_seperated_until(Self::type_expr, Token::ClosingParenthesis)?;
        let ret = self.optional(Self::type_expr, Token::RightArrow)?;
        self.expect(Token::Equals)?;
        let mut branches = vec![self.func_branch()?];
        while self.next_peek_is(&Token::Bar) {
            branches.push(self.func_branch()?);
        }

        Ok(Declaration::Function { name, params, ret, branches })
    }

    fn func_branch(&mut self) -> ParseResult<(Vec<Pattern>, Expression)> {
        let patterns = self.comma_seperated_until(Self::pattern, Token::RightArrow)?;
        let expr = self.expression()?;

        Ok((patterns, expr))
    }

    fn import(&mut self) -> ParseResult<Declaration> {
        self.expect(Token::KeywordImport)?;
        let mut parts = vec![self.expect_identifier()?];
        while self.next_peek_is(&Token::DoubleColon) {
            parts.push(self.expect_identifier()?);
        }

        let mut import_path = parts.iter().fold(self.file_path.clone(), |mut acc, part| {
            acc.push(&*part.data);
            acc
        });

        let kind = Self::parse_import(import_path.clone(), &parts)?;

        let directs = if self.next_peek_is(&Token::OpeningParenthesis) {
            self.comma_seperated_until(Self::expect_identifier, Token::ClosingParenthesis)?
        } else {
            vec![]
        };

        if matches!(kind, ImportKind::File(_)) {
            import_path.set_extension("txt");
        }

        Ok(Declaration::Import { parts, kind, directs, path: import_path.to_str().unwrap().into() })
    }

    fn parse_import(mut import_path: PathBuf, parts: &[Spanned<Symbol>]) -> ParseResult<ImportKind> {
        if import_path.is_dir() {
            let mut imports = vec![];
            for path in read_dir(import_path).unwrap() {
                let mut path = path.unwrap().path();
                let kind = Self::parse_import(path.clone(), parts)?;
                path.set_extension("");
                let name =  path.file_name().unwrap().to_str().unwrap().into();
                imports.push((name, (kind, path.to_str().unwrap().into())));
            }

            Ok(ImportKind::Folder(imports))
        } else {
            // TODO: Do not hardcode the file extension.
            import_path.set_extension("txt");

            // TODO: Remove unwrap.
            let import_file = read_to_string(&import_path).unwrap();
            let import =
                Parser::new(Tokens::new(&import_file), import_path.clone())
                    .declarations()
                    .map_err(|error| {
                        let first = parts.first().unwrap().span;
                        let last = parts.last().unwrap().span;
                        let span = first.extend(last);
                        ParseError::ImportError {
                            import_path: import_path.into_os_string().into_string().unwrap().into_boxed_str(),
                            error: Box::new(error),
                        }
                        .attach(span)
                    })?;

            Ok(ImportKind::File(import))
        }
    }

    fn type_constructor(&mut self) -> ParseResult<(Spanned<Symbol>, Vec<TypeExpression>)> {
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

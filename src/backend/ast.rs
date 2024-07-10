use std::fmt::Display;

use crate::frontend::{
    span::{Span, Spanned},
    token::Symbol,
};

#[derive(Clone, Debug)]
pub struct Application {
    pub expr: Box<Expression>,
    pub args: Vec<Expression>,
}

#[derive(Clone, Debug)]
pub struct Let {
    pub expr: Box<Expression>,
    pub type_expr: Option<TypeExpression>,
    pub branches: Vec<(Pattern, Box<Expression>)>
}

#[derive(Clone, Debug)]
pub struct Access {
    pub path: Vec<Spanned<Symbol>>,
    pub abs_bound: AbsoluteBound,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(Spanned<Symbol>, Bound),
    Integer(Spanned<Symbol>),
    Float(Spanned<Symbol>),
    String(Spanned<Symbol>),
    Nothing(Span),
    Application(Application),
    Let(Let),
    Access(Access),
}

impl Expression {
    pub fn span(&self) -> Span {
        match self {
            Self::Identifier(lexeme, _)
            | Self::Integer(lexeme)
            | Self::Float(lexeme)
            | Self::String(lexeme) => lexeme.span,
            Self::Nothing(span) => *span,
            Self::Application(Application { expr, args: _ }) => expr.span(),
            Self::Let(Let { type_expr: _, expr: _, branches }) => branches.last().unwrap().1.span(),
            Self::Access(Access { path, abs_bound: _, }) => path.first().unwrap().span.extend(path.last().unwrap().span),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Bound {
    Local(usize),
    Absolute(AbsoluteBound),
    None,
}

impl Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(id) => write!(f, "Local {id}"),
            Self::Absolute(abs_bound) => write!(f, "{abs_bound}"),
            Self::None => write!(f, "None"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum AbsoluteBound {
    FromModule {
        module: Symbol,
        name: Symbol
    },
    Constructor {
        module: Symbol,
        typ: Symbol,
        name: Symbol
    },
    Undetermined,
}

impl Display for AbsoluteBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FromModule { module, name } => write!(f, "{module}::{name}"),
            Self::Constructor { module, typ, name } => write!(f, "{module}::{typ}::{name}"),
            Self::Undetermined => write!(f, "Undetermined"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Spanned<Symbol>),
    String(Spanned<Symbol>),
    Integer(Spanned<Symbol>),
    Float(Spanned<Symbol>),
    Constructor {
        path: Vec<Spanned<Symbol>>,
        abs_bound: AbsoluteBound,
        params: Vec<Pattern>,
    }
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Self::Any(lexeme)
            | Self::String(lexeme)
            | Self::Integer(lexeme)
            | Self::Float(lexeme) => lexeme.span,
            Self::Constructor { path, params: _, abs_bound: _ } => {
                path.first().unwrap().span.extend(path.last().unwrap().span)
            },
        }
    }
}

pub enum Declaration {
    Function {
        name: Spanned<Symbol>,
        params: Vec<TypeExpression>,
        ret: Option<TypeExpression>,
        branches: Vec<(Vec<Pattern>, Expression)>
    },
    Import {
        parts: Vec<Spanned<Symbol>>,
        kind: ImportKind,
        directs: Vec<Spanned<Symbol>>,
        path: Symbol,
    },
    Type {
        name: Spanned<Symbol>,
        consts: Vec<(Spanned<Symbol>, Vec<TypeExpression>)>
    }
}

pub enum ImportKind {
    File(Vec<Declaration>),
    Folder(Vec<(Symbol, (ImportKind, Symbol))>)
}

#[derive(Clone, Debug)]
pub struct TypeFunction {
    pub params: Vec<TypeExpression>,
    pub ret: Box<TypeExpression>,
}

#[derive(Clone, Debug)]
pub enum TypeExpression {
    Identifier(Spanned<Symbol>, Bound),
    Function(TypeFunction),
    Access(Vec<Spanned<Symbol>>, AbsoluteBound)
}

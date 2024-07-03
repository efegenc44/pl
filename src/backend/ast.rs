use std::fmt::Display;

use crate::frontend::{
    span::{Span, Spanned},
    token::Symbol,
};

#[derive(Debug)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Less,
    Pow,
}

impl Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Less => write!(f, "<"),
            Self::Pow => write!(f, "^"),
        }
    }
}

#[derive(Debug)]
pub struct Binary {
    pub lhs: Box<Expression>,
    pub op: Operator,
    pub rhs: Box<Expression>,
}

#[derive(Debug)]
pub struct Application {
    pub expr: Box<Expression>,
    pub args: Vec<Expression>,
}

#[derive(Debug)]
pub struct Let {
    pub pattern: Pattern,
    pub type_expr: Option<TypeExpression>,
    pub expr: Box<Expression>,
    pub body: Box<Expression>,
}

#[derive(Debug)]
pub struct Lambda {
    pub params: Vec<Pattern>,
    pub body: Box<Expression>,
}

#[derive(Debug)]
pub struct Access {
    pub path: Vec<Spanned<Symbol>>,
    pub namespace: Namespace,
}

#[derive(Debug)]
pub enum Expression {
    Identifier(Spanned<Symbol>, Bound),
    Integer(Spanned<Symbol>),
    Float(Spanned<Symbol>),
    String(Spanned<Symbol>),
    Nothing(Span),
    Binary(Binary),
    Application(Application),
    Let(Let),
    Lambda(Lambda),
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
            Self::Binary(Binary { lhs, op: _, rhs }) => lhs.span().extend(rhs.span()),
            Self::Application(Application { expr, args: _ }) => expr.span(),
            Self::Let(Let { pattern: _, type_expr: _, expr: _, body }) => body.span(),
            Self::Lambda(Lambda { params: _, body }) => body.span(),
            Self::Access(Access { path, namespace: _ }) => path.first().unwrap().span.extend(path.last().unwrap().span),
        }
    }
}

#[derive(Debug)]
pub enum Namespace {
    Type,
    Module,
    Undetermined
}

#[derive(Debug)]
pub enum Bound {
    Local(usize),
    Global(Symbol),
    None,
}

impl Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(id) => write!(f, "Local {id}"),
            Self::Global(name) => write!(f, "Global {name}"),
            Self::None => write!(f, "None"),
        }
    }
}

#[derive(Debug)]
pub enum Pattern {
    Any(Spanned<Symbol>),
    String(Spanned<Symbol>),
    Integer(Spanned<Symbol>),
    Float(Spanned<Symbol>),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Self::Any(lexeme)
            | Self::String(lexeme)
            | Self::Integer(lexeme)
            | Self::Float(lexeme) => lexeme.span,
        }
    }
}

pub enum Declaration {
    Function {
        name: Spanned<Symbol>,
        params: Vec<TypedPattern>,
        body: Expression,
        ret: Option<TypeExpression>,
    },
    Import {
        parts: Vec<Spanned<Symbol>>,
        kind: ImportKind,
    },
    Type {
        name: Spanned<Symbol>,
        consts: Vec<(Spanned<Symbol>, Vec<TypeExpression>)>
    }
}

pub enum ImportKind {
    File(Vec<Declaration>),
    Folder(Vec<(Symbol, ImportKind)>)
}

#[derive(Debug)]
pub struct TypeFunction {
    pub params: Vec<TypeExpression>,
    pub ret: Box<TypeExpression>,
}

#[derive(Debug)]
pub enum TypeExpression {
    Identifier(Spanned<Symbol>, Bound),
    Function(TypeFunction),
    Access(Vec<Spanned<Symbol>>)
}

pub struct TypedPattern {
    pub pattern: Pattern,
    pub typ: TypeExpression,
}


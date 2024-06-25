use std::{collections::HashMap, fmt::Display, usize};

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
pub enum Expression {
    Identifier(Spanned<Symbol>, Bound),
    Integer(Spanned<Symbol>),
    Float(Spanned<Symbol>),
    String(Spanned<Symbol>),
    Nothing(Span),
    Binary {
        lhs: Box<Expression>,
        op: Operator,
        rhs: Box<Expression>,
    },
    Application {
        expr: Box<Expression>,
        args: Vec<Expression>,
    },
    Let {
        pattern: Pattern,
        typ: Option<TypeExpr>,
        expr: Box<Expression>,
        body: Box<Expression>,
    },
    Lambda {
        params: Vec<Pattern>,
        body: Box<Expression>,
    },
    Access {
        module_name: Spanned<Symbol>,
        name: Spanned<Symbol>,
    },
}

impl Expression {
    pub fn span(&self) -> Span {
        match self {
            Self::Identifier(lexeme, _)
            | Self::Integer(lexeme)
            | Self::Float(lexeme)
            | Self::String(lexeme) => lexeme.span,
            Self::Nothing(span) => *span,
            Self::Binary { lhs, op: _, rhs } => lhs.span().extend(rhs.span()),
            Self::Application { expr, args: _ } => expr.span(),
            Self::Let { pattern: _, typ: _, expr: _, body } => body.span(),
            Self::Lambda { params: _, body } => body.span(),
            Self::Access { module_name, name } => module_name.span.extend(name.span),
        }
    }
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
        ret: Option<TypeExpr>,
    },
    Import {
        parts: Vec<Spanned<Symbol>>,
    },
}

#[derive(Debug)]
pub enum TypeExpr {
    Identifier(Spanned<Symbol>, Bound),
    Function {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
    },
}

pub struct TypedPattern {
    pub pattern: Pattern,
    pub typ: TypeExpr,
}

pub struct Import {
    pub span: Span,
    pub import_path: Symbol,
    pub module: Module,
}

impl Import {
    pub fn new(span: Span, import_path: Symbol, module: Module) -> Self {
        Self {
            span,
            import_path,
            module,
        }
    }
}

pub struct Module {
    pub decls: HashMap<Symbol, Declaration>,
    pub imports: HashMap<Symbol, Import>,
}

impl Module {
    pub fn new(decls: HashMap<Symbol, Declaration>, imports: HashMap<Symbol, Import>) -> Self {
        Self { decls, imports }
    }
}

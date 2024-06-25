use std::{collections::HashMap, fmt::Display, usize};

use crate::frontend::{
    span::{HasSpan, Span, Spanned},
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
    pub fn pretty_print(&self) {
        self._pretty_print(0);
    }

    fn _pretty_print(&self, depth: usize) {
        fn indented<T: Display>(msg: T, depth: usize) {
            print!("{:1$}{msg}", "", depth * 2);
        }

        match self {
            Self::Identifier(identifier, bound) => println!("{} {bound}", identifier.data),
            Self::Integer(literal) | Self::Float(literal) | Self::String(literal) => {
                println!("{}", literal.data)
            }
            Self::Binary { lhs, op, rhs } => {
                println!("Binary:");
                indented(format!("op: {op}\n"), depth + 1);
                indented("lhs: ", depth + 1);
                lhs._pretty_print(depth + 1);
                indented("rhs: ", depth + 1);
                rhs._pretty_print(depth + 1);
            }
            Self::Application { expr, args } => {
                println!("Application:");
                indented("expr: ", depth + 1);
                expr._pretty_print(depth + 1);
                indented("args:\n", depth + 1);
                for arg in args {
                    indented("", depth + 2);
                    arg._pretty_print(depth + 2);
                }
            }
            Self::Let {
                pattern,
                expr,
                body,
            } => {
                println!("Let:");
                indented("pattern: ", depth + 1);
                pattern._pretty_print(depth + 1);
                indented("expr: ", depth + 1);
                expr._pretty_print(depth + 1);
                indented("body: ", depth + 1);
                body._pretty_print(depth + 1);
            }
            Self::Lambda { params, body } => {
                println!("Lambda:");
                indented("params:\n", depth + 1);
                for param in params {
                    indented("", depth + 2);
                    param._pretty_print(depth + 2);
                }
                indented("body: ", depth + 1);
                body._pretty_print(depth + 1);
            }
            Self::Access { module_name, name } => {
                println!("Access:");
                indented(format!("module: {}\n", module_name.data), depth + 1);
                indented(format!("name: {}\n", name.data), depth + 1);
            }
        }
    }
}

impl HasSpan for Expression {}

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
    fn _pretty_print(&self, _depth: usize) {
        match self {
            Self::Any(literal)
            | Self::String(literal)
            | Self::Integer(literal)
            | Self::Float(literal) => println!("{}", literal.data),
        }
    }
}

impl HasSpan for Pattern {}

pub enum Declaration {
    Function {
        name: Spanned<Symbol>,
        params: Vec<Pattern>,
        body: Expression,
    },
    Import {
        parts: Vec<Spanned<Symbol>>,
    },
}

impl Declaration {
    pub fn pretty_print(&self) {
        self._pretty_print(0)
    }

    fn _pretty_print(&self, depth: usize) {
        fn indented<T: Display>(msg: T, depth: usize) {
            print!("{:1$}{msg}", "", depth * 2);
        }

        match self {
            Self::Function { name, params, body } => {
                println!("Func:");
                indented(format!("name: {}\n", name.data), depth + 1);
                indented("params:\n", depth + 1);
                for param in params {
                    indented("", depth + 2);
                    param._pretty_print(depth + 2);
                }
                indented("expr: ", depth + 1);
                body._pretty_print(depth + 1);
            }
            Self::Import { parts } => {
                println!("Import:");
                indented("parts:\n", depth + 1);
                for part in parts {
                    indented(format!("{}\n", part.data), depth + 2);
                }
            }
        }
    }
}

impl HasSpan for Declaration {}

pub struct Import {
    pub span: Span,
    pub import_path: Symbol,
    pub module: Module,
}

impl Import {
    pub fn new(span: Span, import_path: Symbol, module: Module) -> Self {
        Self { span, import_path, module }
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

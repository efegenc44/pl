use std::{collections::HashMap, fmt::Display, usize};

use crate::frontend::{
    span::{HasSpan, Spanned},
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
    Identifier(Symbol, Bound),
    Integer(Symbol),
    Float(Symbol),
    String(Symbol),
    Binary {
        lhs: Box<Spanned<Expression>>,
        op: Operator,
        rhs: Box<Spanned<Expression>>,
    },
    Application {
        expr: Box<Spanned<Expression>>,
        args: Vec<Spanned<Expression>>,
    },
    Let {
        pattern: Spanned<Pattern>,
        expr: Box<Spanned<Expression>>,
        body: Box<Spanned<Expression>>,
    },
    Lambda {
        params: Vec<Spanned<Pattern>>,
        body: Box<Spanned<Expression>>,
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
            Self::Identifier(identifier, bound) => println!("{identifier} {bound}"),
            Self::Integer(literal) | Self::Float(literal) | Self::String(literal) => {
                println!("{literal}")
            }
            Self::Binary { lhs, op, rhs } => {
                println!("Binary:");
                indented(format!("op: {op}\n"), depth + 1);
                indented("lhs: ", depth + 1);
                lhs.data._pretty_print(depth + 1);
                indented("rhs: ", depth + 1);
                rhs.data._pretty_print(depth + 1);
            }
            Self::Application { expr, args } => {
                println!("Application:");
                indented("expr: ", depth + 1);
                expr.data._pretty_print(depth + 1);
                indented("args:\n", depth + 1);
                for arg in args {
                    indented("", depth + 2);
                    arg.data._pretty_print(depth + 2);
                }
            }
            Self::Let {
                pattern,
                expr,
                body,
            } => {
                println!("Let:");
                indented("pattern: ", depth + 1);
                pattern.data._pretty_print(depth + 1);
                indented("expr: ", depth + 1);
                expr.data._pretty_print(depth + 1);
                indented("body: ", depth + 1);
                body.data._pretty_print(depth + 1);
            }
            Self::Lambda { params, body } => {
                println!("Lambda:");
                indented("params:\n", depth + 1);
                for param in params {
                    indented("", depth + 2);
                    param.data._pretty_print(depth + 2);
                }
                indented("body: ", depth + 1);
                body.data._pretty_print(depth + 1);
            }
            Self::Access {
                module_name: module,
                name,
            } => {
                println!("Access:");
                indented(format!("module: {}\n", module.data), depth + 1);
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
    Any(Symbol),
    String(Symbol),
    Integer(Symbol),
    Float(Symbol),
}

impl Pattern {
    fn _pretty_print(&self, _depth: usize) {
        match self {
            Self::Any(literal)
            | Self::String(literal)
            | Self::Integer(literal)
            | Self::Float(literal) => println!("{literal}"),
        }
    }
}

impl HasSpan for Pattern {}

pub enum Declaration {
    Function {
        name: Spanned<Symbol>,
        params: Vec<Spanned<Pattern>>,
        body: Spanned<Expression>,
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
            Self::Function {
                name,
                params,
                body: expr,
            } => {
                println!("Func:");
                indented(format!("name: {}\n", name.data), depth + 1);
                indented("params:\n", depth + 1);
                for param in params {
                    indented("", depth + 2);
                    param.data._pretty_print(depth + 2);
                }
                indented("expr: ", depth + 1);
                expr.data._pretty_print(depth + 1);
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

pub struct Module {
    pub decls: HashMap<Symbol, Spanned<Declaration>>,
    pub imports: HashMap<Symbol, Module>,
}

impl Module {
    pub fn new(
        decls: HashMap<Symbol, Spanned<Declaration>>,
        imports: HashMap<Symbol, Module>,
    ) -> Self {
        Self { decls, imports }
    }
}

use std::{fmt::Display, usize};

use crate::frontend::span::{HasSpan, Spanned};

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
pub enum Expression<'source> {
    Identifier(&'source str, Bound),
    Integer(&'source str),
    Float(&'source str),
    String(&'source str),
    Binary {
        lhs: Box<Spanned<'source, Expression<'source>>>,
        op: Operator,
        rhs: Box<Spanned<'source, Expression<'source>>>,
    },
    Application {
        expr: Box<Spanned<'source, Expression<'source>>>,
        args: Vec<Spanned<'source, Expression<'source>>>,
    },
    Let {
        pattern: Spanned<'source, Pattern<'source>>,
        expr: Box<Spanned<'source, Expression<'source>>>,
        body: Box<Spanned<'source, Expression<'source>>>,
    },
    Lambda {
        params: Vec<Spanned<'source, Pattern<'source>>>,
        body: Box<Spanned<'source, Expression<'source>>>,
    },
}

impl<'source> Expression<'source> {
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
        }
    }
}

impl HasSpan for Expression<'_> {}

#[derive(Debug)]
pub enum Bound {
    Local(usize),
    None,
}

impl Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(id) => write!(f, "Local {id}"),
            Self::None => write!(f, "None"),
        }
    }
}

#[derive(Debug)]
pub enum Pattern<'source> {
    Any(&'source str),
    String(&'source str),
    Integer(&'source str),
    Float(&'source str),
}

impl<'source> Pattern<'source> {
    fn _pretty_print(&self, _depth: usize) {
        match self {
            Self::Any(literal)
            | Self::String(literal)
            | Self::Integer(literal)
            | Self::Float(literal) => println!("{literal}"),
        }
    }
}

impl HasSpan for Pattern<'_> {}

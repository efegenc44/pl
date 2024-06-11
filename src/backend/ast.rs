use crate::frontend::span::{Span, Spanned};

#[derive(Debug)]
pub enum Expression<'source> {
    Identifier(&'source str),
    Integer(&'source str),
    Float(&'source str),
    String(&'source str),
    Binary {
        lhs: Box<Spanned<'source, Expression<'source>>>,
        op: &'source str,
        rhs: Box<Spanned<'source, Expression<'source>>>,
    },
    Application {
        expr: Box<Spanned<'source, Expression<'source>>>,
        args: Vec<Spanned<'source, Expression<'source>>>,
    },
}

impl<'source> Expression<'source> {
    pub fn pretty_print(&self) {
        self._pretty_print(0);
    }

    fn _pretty_print(&self, depth: usize) {
        let indent = (depth + 1) * 2;

        match self {
            Self::Identifier(literal)
            | Self::Integer(literal)
            | Self::Float(literal)
            | Self::String(literal) => println!("{literal}"),
            Self::Binary { lhs, op, rhs } => {
                println!("{op}");
                print!("{:>indent$}", "");
                lhs.data._pretty_print(depth + 1);
                print!("{:>indent$}", "");
                rhs.data._pretty_print(depth + 1);
            }
            Self::Application { expr, args } => {
                expr.data._pretty_print(depth);
                for arg in args {
                    print!("{:>indent$}", "");
                    arg.data._pretty_print(depth + 1);
                }
            }
        }
    }

    pub fn attach(self, span: Span<'source>) -> Spanned<'source, Self> {
        Spanned::new(self, span)
    }
}

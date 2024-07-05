use crate::frontend::token::Symbol;

use super::ast::{Expression, Pattern};

#[derive(Clone)]
pub enum Value {
    Integer(isize),
    Float(f32),
    String(String),
    Nothing,
    Custom {
        constructor: Symbol,
        values: Vec<Value>
    },
    Function(FunctionValue),
    Constructor(Symbol, usize)
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(lit) => write!(f, "{lit}"),
            Self::Float(lit) => write!(f, "{lit}"),
            Self::String(lit) => write!(f, "{lit}"),
            Self::Nothing => write!(f, "nothing"),
            Self::Custom { constructor, values } => {
                write!(f, "{constructor}")?;

                if values.len() == 0 {
                    return Ok(());
                }

                write!(f, "(")?;
                for value in &values[..values.len() - 1] {
                    write!(f, "{value}, ")?;
                }
                write!(f, "{})", values.last().unwrap())
            },
            Self::Function(_) => write!(f, "<function>"),
            Self::Constructor(_, _) => write!(f, "<function>"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionValue {
    pub branches: Vec<(Vec<Pattern>, Expression)>,
}

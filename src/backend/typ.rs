use std::fmt::Display;

use crate::frontend::token::Symbol;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Nothing,
    Integer,
    Float,
    String,
    Function {
        params: Vec<Type>,
        ret: Box<Type>
    },
    Custom(Symbol),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nothing => write!(f, "Nothing"),
            Self::Integer => write!(f, "Integer"),
            Self::Float => write!(f, "Float"),
            Self::String => write!(f, "String"),
            Self::Function { params, ret } => {
                write!(f, "(")?;
                if let [rest@.., last] = &params[..] {
                    for param in rest {
                        write!(f, "{param}, ")?;
                    }
                    write!(f, "{last}")?;
                }
                write!(f, ")")?;
                write!(f, " -> ")?;
                write!(f, "{ret}")
            },
            Self::Custom(name) => write!(f, "{name}")
        }
    }
}

use std::fmt::Display;

use crate::frontend::token::Symbol;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Nothing,
    Integer,
    Float,
    String,
    Function {
        vars: Option<Vec<Symbol>>,
        params: Vec<Type>,
        ret: Box<Type>
    },
    Custom(Option<Vec<Symbol>>, Symbol),
    Composite(Symbol, Vec<Type>),
    Variable(usize),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nothing => write!(f, "Nothing"),
            Self::Integer => write!(f, "Integer"),
            Self::Float => write!(f, "Float"),
            Self::String => write!(f, "String"),
            Self::Function { vars, params, ret } => {
                if let Some(vars) = vars {
                    write!(f, "(")?;
                    if let [rest@.., last] = &vars[..] {
                        for param in rest {
                            write!(f, "{param}, ")?;
                        }
                        write!(f, "{last}")?;
                    }
                    write!(f, ") ")?;
                }

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
            Self::Custom(vars, name) => {
                if let Some(vars) = vars {
                    write!(f, "(")?;
                    if let [rest@.., last] = &vars[..] {
                        for param in rest {
                            write!(f, "{param}, ")?;
                        }
                        write!(f, "{last}")?;
                    }
                    write!(f, ") ")?;
                }

                write!(f, "{name}")
            },
            Self::Composite(name, args) => {
                write!(f, "{name}")?;
                write!(f, "(")?;
                if let [rest@.., last] = &args[..] {
                    for param in rest {
                        write!(f, "{param}, ")?;
                    }
                    write!(f, "{last}")?;
                }
                write!(f, ")")
            },
            Self::Variable(indice) => write!(f, "{indice}"),
        }
    }
}

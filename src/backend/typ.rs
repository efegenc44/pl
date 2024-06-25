use std::fmt::Display;

#[derive(Clone, PartialEq, Eq)]
pub enum Type {
    Nothing,
    Integer,
    Float,
    String,
    Function {
        params: Vec<Type>,
        ret: Box<Type>
    }
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
        }
    }
}

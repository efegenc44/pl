use std::rc::Rc;

use crate::frontend::token::Symbol;

use super::ast::{Expression, Pattern};

#[derive(Clone)]
pub enum Value {
    Integer(isize),
    Float(f32),
    String(String),
    Nothing,
    Custom(CustomValue),
    Function(FunctionValue),
    Constructor(Symbol)
}

impl Value {
    pub fn custom(constructor: Symbol, values: Vec<Value>) -> Value {
        Value::Custom(Rc::new(CustomInstance { constructor, values }))
    }
}

pub struct FunctionInstance {
    pub branches: Vec<(Vec<Pattern>, Expression)>,
}
pub type FunctionValue = Rc<FunctionInstance>;

pub struct CustomInstance {
    pub constructor: Symbol,
    pub values: Vec<Value>
}
pub type CustomValue = Rc<CustomInstance>;


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
            Self::Custom(custom) => {
                write!(f, "{}", &custom.constructor)?;
                match &custom.values[..] {
                    [rest@.., last] => {
                        write!(f, "(")?;
                        for value in rest {
                            write!(f, "{value}, ")?;
                        }
                        write!(f, "{last})")
                    }
                    [] => Ok(())
                }
            },
            Self::Function(_) => write!(f, "<function>"),
            Self::Constructor(_) => write!(f, "<function>"),
        }
    }
}

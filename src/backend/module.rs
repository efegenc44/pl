use std::{collections::HashMap, fmt::Display};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::ast::{Declaration, Expression, TypeExpr, TypedPattern};

#[derive(Default)]
pub struct Module {
    pub functions: HashMap<Symbol, Function>,
    pub imports: HashMap<Symbol, Import>,
    pub types: HashMap<Symbol, Type>,
}

impl Module {
    pub fn new(declarations: Vec<Declaration>) -> ModuleResult<Self> {
        let mut functions = HashMap::new();
        let mut imports = HashMap::new();
        let mut types = HashMap::new();

        for declaration in declarations {
            match declaration {
                Declaration::Function { name, params, body, ret } => {
                    if !functions.contains_key(&name.data) {
                        functions.insert(name.data.clone(), Function { name, params, body, ret });
                    } else {
                        return Err(ModuleError::DuplicateDeclaration(name.data.clone()).attach(name.span))
                    }
                }
                Declaration::Import { parts, import } => {
                    let module = Module::new(import)
                        .map_err(|error| {
                            // TODO: Do not hardcode the file extension.
                            let import_path = parts.iter().fold(String::from("."), |mut acc, part| {
                                acc.push('\\');
                                acc.push_str(&part.data);
                                acc
                            }) + ".txt";

                            let first = parts.first().unwrap().span;
                            let last = parts.last().unwrap().span;
                            let span = first.extend(last);
                            ModuleError::ImportError {
                                import_path: import_path.into(),
                                error: Box::new(error),
                            }
                            .attach(span)
                        })?;

                    let module_name = parts.last().unwrap().data.clone();
                    imports.insert(module_name, Import { parts, module });
                },
                Declaration::Type { name, consts } => {
                    if !types.contains_key(&name.data) {
                        types.insert(name.data.clone(), Type { name, consts });
                    } else {
                        return Err(ModuleError::DuplicateDeclaration(name.data.clone()).attach(name.span))
                    }
                }
            }
        }

        Ok(Self { functions, imports, types })
    }
}

pub enum ModuleError {
    DuplicateDeclaration(Symbol),
    ImportError {
        import_path: Symbol,
        error: Box<Spanned<ModuleError>>
    }
}

impl HasSpan for ModuleError {}

impl Display for ModuleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateDeclaration(identifier) => write!(f, "`{identifier}` has already declared."),
            Self::ImportError { .. } => write!(f, "Error while importing module."),
        }
    }
}

pub type ModuleResult<T> = Result<T, Spanned<ModuleError>>;

pub struct Function {
    pub name: Spanned<Symbol>,
    pub params: Vec<TypedPattern>,
    pub body: Expression,
    pub ret: Option<TypeExpr>,
}

pub struct Import {
    pub parts: Vec<Spanned<Symbol>>,
    pub module: Module,
}

pub struct Type {
    pub name: Spanned<Symbol>,
    pub consts: Vec<(Spanned<Symbol>, Vec<TypeExpr>)>
}

use std::{collections::HashMap, fmt::Display};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::ast::{self, Declaration, Expression, Pattern, TypeExpression};

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
                Declaration::Function { name, params, ret, branches  } => {
                    if !functions.contains_key(&name.data) {
                        functions.insert(name.data.clone(), Function { name, params, ret, branches  });
                    } else {
                        return Err(ModuleError::DuplicateDeclaration(name.data.clone()).attach(name.span))
                    }
                }
                Declaration::Import { parts, kind, directs } => {
                    let module_name = parts.last().unwrap().data.clone();
                    imports.insert(module_name, Import { kind: Self::import_kind(kind, &parts)?, parts, directs });
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

    fn import_kind(kind: ast::ImportKind, parts: &[Spanned<Symbol>]) -> ModuleResult<ImportKind> {
        match kind {
            ast::ImportKind::File(import) => {
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

                Ok(ImportKind::File(module))
            },
            ast::ImportKind::Folder(imports) => {
                let mut map = HashMap::new();
                for (name, kind) in imports {
                    let kind = Self::import_kind(kind, parts)?;
                    map.insert(name, Import { parts: parts.to_vec(), kind, directs: vec![] });
                }

                Ok(ImportKind::Folder(map))
            },
        }
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
    pub params: Vec<TypeExpression>,
    pub ret: Option<TypeExpression>,
    pub branches: Vec<(Vec<Pattern>, Expression)>,
}

pub struct Import {
    pub parts: Vec<Spanned<Symbol>>,
    pub kind: ImportKind,
    pub directs: Vec<Spanned<Symbol>>,
}

pub struct Type {
    pub name: Spanned<Symbol>,
    pub consts: Vec<(Spanned<Symbol>, Vec<TypeExpression>)>
}

pub enum ImportKind {
    File(Module),
    Folder(HashMap<Symbol, Import>)
}

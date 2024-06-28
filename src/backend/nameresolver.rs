use std::{
    collections::{HashMap, HashSet}, fmt::Display
};

use crate::frontend::{
    span::{HasSpan, Spanned},
    token::Symbol,
};

use super::{ast::{Bound, Expression, Namespace, Pattern, TypeExpr, TypedPattern}, module::{self, Function, Import, Module}};

pub struct NameResolver {
    locals: Vec<Symbol>,
    types: HashMap<Symbol, HashSet<Symbol>>,
    functions: HashSet<Symbol>,
    imports: HashMap<Symbol, Import>,
}

impl NameResolver {
    pub fn new() -> Self {
        // let _primitive_types: HashMap<Symbol, module::Type> = HashMap::from([
        //     ("Integer".into(), module::Type {}),
        //     ("String".into(), module::Type {}),
        //     ("Float".into(), module::Type {}),
        //     ("Nothing".into(), module::Type {}),
        // ]);

        Self {
            locals: Vec::new(),
            types: HashMap::new(),
            functions: HashSet::new(),
            imports: HashMap::new(),
        }
    }

    pub fn resolve_expr(&mut self, expr: Expression) -> ResolutionResult<Expression> {
        let resolved_expr = match expr {
            Expression::Integer(_) | Expression::Float(_) | Expression::String(_) | Expression::Nothing(_) => expr,
            Expression::Identifier(identifier, _) => {
                if let Some(indice) = self
                    .locals
                    .iter()
                    .rev()
                    .position(|local| local == &identifier.data)
                {
                    Expression::Identifier(identifier, Bound::Local(indice))
                } else {
                    let true = self.functions.contains(&identifier.data) else {
                        return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
                    };
                    let name = identifier.data.clone();
                    Expression::Identifier(identifier, Bound::Global(name))
                }
            }
            Expression::Binary { lhs, op, rhs } => Expression::Binary {
                lhs: Box::new(self.resolve_expr(*lhs)?),
                op,
                rhs: Box::new(self.resolve_expr(*rhs)?),
            },
            Expression::Application { expr, args } => Expression::Application {
                expr: Box::new(self.resolve_expr(*expr)?),
                args: args
                    .into_iter()
                    .map(|arg| self.resolve_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Expression::Let { pattern, typ, expr, body } => {
                let expr = Box::new(self.resolve_expr(*expr)?);
                let typ = if let Some(typ) = typ {
                    Some(self.resolve_type_expr(typ)?)
                } else {
                    None
                };
                let local_count = self.push_names_in_pattern(&pattern);
                let body = Box::new(self.resolve_expr(*body)?);
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Let { pattern, typ, expr, body }
            }
            Expression::Lambda { params, body } => {
                let local_count = params
                    .iter()
                    .map(|param| self.push_names_in_pattern(param))
                    .sum::<usize>();
                let body = Box::new(self.resolve_expr(*body)?);
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Lambda { params, body }
            }
            Expression::Access { path, namespace: _ } => {
                match &path[..] {
                    [_] | [] => unreachable!(),
                    [from, name] => {
                        if let Some(import) = self.imports.get(&from.data) {
                            let true = import.module.functions.contains_key(&name.data) else {
                                let span = from.span.extend(name.span);
                                return Err(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(span))
                            };
                            Expression::Access { path, namespace: Namespace::Import }
                        } else if let Some(typ) = self.types.get(&from.data) {
                            let true = typ.contains(&name.data) else {
                                let span = from.span.extend(name.span);
                                return Err(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(span))
                            };
                            Expression::Access { path, namespace: Namespace::Type }
                        } else {
                            return Err(ResolutionError::NonExistantModule(from.data.clone()).attach(from.span))
                        }
                    },
                    // In this case modules.len() >= 1 and they have to refer to a module.
                    [modules@.., before, last] => {
                        let from = &modules.first().unwrap();
                        let Some(mut current_import) = self.imports.get(&from.data) else {
                            return Err(ResolutionError::NonExistantModule(from.data.clone()).attach(from.span))
                        };

                        for module in &modules[1..] {
                            let Some(import) = current_import.module.imports.get(&module.data) else {
                                return Err(ResolutionError::NonExistantModule(module.data.clone()).attach(module.span))
                            };

                            current_import = import;
                        }

                        if let Some(import) = current_import.module.imports.get(&before.data) {
                            let true = import.module.functions.contains_key(&last.data) else {
                                let span = before.span.extend(last.span);
                                return Err(ResolutionError::UnboundInModule { module_name: before.data.clone(), name: last.data.clone() }.attach(span))
                            };
                            Expression::Access { path, namespace: Namespace::Import }
                        } else if let Some(typ) = current_import.module.types.get(&before.data) {
                            let true = typ.consts.iter().any(|(x, _)| &x.data == &last.data) else {
                                let span = before.span.extend(last.span);
                                return Err(ResolutionError::UnboundInModule { module_name: before.data.clone(), name: last.data.clone() }.attach(span))
                            };
                            Expression::Access { path, namespace: Namespace::Type }
                        } else {
                            return Err(ResolutionError::NonExistantModule(before.data.clone()).attach(before.span))
                        }
                    },
                }
            }
        };

        Ok(resolved_expr)
    }

    fn resolve_type_expr(&mut self, type_expr: TypeExpr) -> ResolutionResult<TypeExpr> {
        let resolved_type_expr = match type_expr {
            // TODO: Local type variables for polyphormic types.
            TypeExpr::Identifier(identifier, _) => {
                let Some(_) = self.types.get(&identifier.data) else {
                    return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
                };
                let name = identifier.data.clone();
                TypeExpr::Identifier(identifier, Bound::Global(name))
            }
            TypeExpr::Function { params, ret } => TypeExpr::Function {
                ret: Box::new(self.resolve_type_expr(*ret)?),
                params: params
                    .into_iter()
                    .map(|arg| self.resolve_type_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            TypeExpr::Access { path } => {
                match &path[..] {
                    [_] | [] => unreachable!(),
                    [from, name] => {
                        let Some(import) = self.imports.get(&from.data) else {
                            return Err(ResolutionError::NonExistantModule(from.data.clone()).attach(from.span))
                        };

                        let true = import.module.types.contains_key(&name.data) else {
                            let span = from.span.extend(name.span);
                            return Err(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(span))
                        };

                        TypeExpr::Access { path }
                    },
                    // In this case modules.len() >= 1 and they have to refer to a module.
                    [modules@.., before, last] => {
                        let from = &modules.first().unwrap();
                        let Some(mut current_import) = self.imports.get(&from.data) else {
                            return Err(ResolutionError::NonExistantModule(from.data.clone()).attach(from.span))
                        };

                        for module in &modules[1..] {
                            let Some(import) = current_import.module.imports.get(&module.data) else {
                                return Err(ResolutionError::NonExistantModule(module.data.clone()).attach(module.span))
                            };

                            current_import = import;
                        }

                        let Some(import) = current_import.module.imports.get(&before.data) else {
                            return Err(ResolutionError::NonExistantModule(before.data.clone()).attach(before.span))
                        };

                        let true = import.module.types.contains_key(&last.data) else {
                            let span = before.span.extend(last.span);
                            return Err(ResolutionError::UnboundInModule { module_name: before.data.clone(), name: last.data.clone() }.attach(span))
                        };

                        TypeExpr::Access { path }
                    },
                }
            }
        };

        Ok(resolved_type_expr)
    }

    fn resolve_function(&mut self, Function { name, params, body, ret }: Function) -> ResolutionResult<Function> {
        let mut resolved_params = vec![];
        let mut local_count = 0;
        for TypedPattern { pattern, typ } in params {
            local_count += self.push_names_in_pattern(&pattern);
            resolved_params.push(TypedPattern {
                typ: self.resolve_type_expr(typ)?,
                pattern,
            })
        }
        let body = self.resolve_expr(body)?;
        self.locals.truncate(self.locals.len() - local_count);
        assert!(self.locals.is_empty());

        let ret = if let Some(ret) = ret {
            Some(self.resolve_type_expr(ret)?)
        } else {
            None
        };

        Ok(Function { name, params: resolved_params, body, ret })
    }

    fn resolve_functions(&mut self, functions: HashMap<Symbol, Function>) -> ResolutionResult<HashMap<Symbol, Function>> {
        let mut resolved_functions = HashMap::new();
        for (name, function) in functions {
            resolved_functions.insert(name, self.resolve_function(function)?);
        }

        Ok(resolved_functions)
    }

    fn resolve_types(&mut self, types: HashMap<Symbol, module::Type>) -> ResolutionResult<HashMap<Symbol, module::Type>> {
        let mut resolved_types = HashMap::new();
        for (type_name, module::Type { name, consts }) in types {
            let mut resolved_consts = vec![];
            for (name, params) in consts {
                let params = params.into_iter().map(|param| self.resolve_type_expr(param)).collect::<Result<Vec<_>, _>>()?;
                resolved_consts.push((name, params));
            }
            resolved_types.insert(type_name, module::Type { name, consts: resolved_consts });
        }

        Ok(resolved_types)
    }

    fn resolve_imports(imports: HashMap<Symbol, Import>) -> ResolutionResult<HashMap<Symbol, Import>> {
        let mut resolved_imports = HashMap::new();
        for (name, Import { parts, module }) in imports {
            let module = NameResolver::new().resolve_module(module).map_err(|error| {
                // TODO: Do not hardcode the file extension.
                let import_path = parts.iter().fold(String::from("."), |mut acc, part| {
                    acc.push('\\');
                    acc.push_str(&part.data);
                    acc
                }) + ".txt";

                let first = parts.first().unwrap().span;
                let last = parts.last().unwrap().span;
                let span = first.extend(last);
                ResolutionError::ImportError {
                    import_path: import_path.into(),
                    error: Box::new(error),
                }
                .attach(span)
            })?;

            let resolved_import = Import { parts, module };
            resolved_imports.insert(name, resolved_import);
        }

        Ok(resolved_imports)
    }

    pub fn resolve_module(mut self, module: Module) -> ResolutionResult<Module> {
        for (type_name, module::Type { name: _, consts }) in &module.types {
           self.types.insert(type_name.clone(), consts.iter().map(|(name, _ )| name.data.clone()).collect());
        }
        self.functions = module.functions.keys().cloned().collect();
        self.imports = Self::resolve_imports(module.imports)?;
        let types = self.resolve_types(module.types)?;
        let functions = self.resolve_functions(module.functions)?;

        Ok(Module { functions, imports: self.imports, types })
    }

    fn push_names_in_pattern(&mut self, pattern: &Pattern) -> usize {
        match pattern {
            Pattern::Any(identifier) => {
                self.locals.push(identifier.data.clone());
                1
            }
            _literal => 0,
        }
    }
}

#[derive(Debug)]
pub enum ResolutionError {
    UnboundIdentifier(Symbol),
    NonExistantModule(Symbol),
    UnboundInModule {
        module_name: Symbol,
        name: Symbol,
    },
    ImportError {
        import_path: Symbol,
        error: Box<Spanned<ResolutionError>>,
    },
}

impl Display for ResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundIdentifier(identifier) => write!(f, "`{identifier}` is not bound."),
            Self::NonExistantModule(module) => write!(f, "Module `{module}` does not exist."),
            Self::UnboundInModule { module_name, name } => {
                write!(f, "`{name}` is not bound in module `{module_name}`.")
            }
            Self::ImportError { .. } => write!(f, "Error while importing module."),
        }
    }
}

impl HasSpan for ResolutionError {}

type ResolutionResult<T> = Result<T, Spanned<ResolutionError>>;

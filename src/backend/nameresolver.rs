use std::{
    collections::{HashMap, HashSet}, fmt::Display
};

use crate::{backend::ast::Binary, frontend::{
    span::{HasSpan, Spanned},
    token::Symbol,
}};

use super::{
    ast::{Access, Application, Bound, Expression, TypeFunction, Lambda, Let, Namespace, Pattern, TypeExpression, TypedPattern},
    module::{self, Function, Import, Module}
};

pub struct NameResolver {
    names: Names,
    locals: Vec<Symbol>,
}

impl NameResolver {
    pub fn new(module: &Module) -> Self {
        Self {
            names: Self::collect_names(module),
            locals: Vec::new(),
        }
    }

    pub fn resolve_module(module: Module) -> ResolutionResult<Module> {
        let mut resolver = Self::new(&module);

        Ok(Module {
            functions: resolver.resolve_functions(module.functions)?,
            imports: Self::resolve_imports(module.imports)?,
            types: resolver.resolve_types(module.types)?
        })
    }

    fn collect_names(module: &Module) -> Names {
        let types = module.types.iter().map(|(type_name, typ)| {
            (type_name.clone(), typ.consts.iter().map(|(name, _)| name.data.clone()).collect())
        }).collect();

        let functions = module.functions.keys().cloned().collect();

        let imports = module.imports.iter().map(|(module_name, import)| {
            (module_name.clone(), Self::collect_import_names(&import))
        }).collect();

        Names { functions, imports, types }
    }

    fn collect_import_names(import: &Import) -> ImportNames {
        match &import.kind {
            module::ImportKind::File(module) => {
                let types = module.types.iter().map(|(type_name, typ)| {
                    (type_name.clone(), typ.consts.iter().map(|(name, _)| name.data.clone()).collect())
                }).collect();

                let functions = module.functions.keys().cloned().collect();

                ImportNames::Module { functions, types }
            },
            module::ImportKind::Folder(imports) => {
                let modules = imports.iter().map(|(name, import)| (name.clone(), Self::collect_import_names(import))).collect();

                ImportNames::Group(modules)
            },
        }

    }

    pub fn resolve_expr(&mut self, expr: Expression) -> ResolutionResult<Expression> {
        match expr {
            Expression::Identifier(identifier, _) => self.resolve_identifier(identifier),
            Expression::Binary(binary) => self.resolve_binary(binary),
            Expression::Application(application) => self.resolve_application(application),
            Expression::Let(lett) => self.resolve_let(lett),
            Expression::Lambda(lambda) => self.resolve_lambda(lambda),
            Expression::Access(access) => self.resolve_access(access),
            literal => Ok(literal),
        }
    }

    fn resolve_identifier(&mut self, identifier: Spanned<Symbol>) -> ResolutionResult<Expression> {
        let bound = if let Some(indice) = self.locals.iter().rev().position(|local| local == &identifier.data) {
            Bound::Local(indice)
        } else if self.names.functions.contains(&identifier.data) {
            Bound::Global(identifier.data.clone())
        } else {
            return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
        };

        Ok(Expression::Identifier(identifier, bound))
    }

    fn resolve_binary(&mut self, Binary { lhs, op, rhs }: Binary) -> ResolutionResult<Expression> {
        let lhs = Box::new(self.resolve_expr(*lhs)?);
        let rhs = Box::new(self.resolve_expr(*rhs)?);

        Ok(Expression::Binary(Binary { lhs, op, rhs }))
    }

    fn resolve_application(&mut self, Application { expr, args }: Application) -> ResolutionResult<Expression> {
        let expr = Box::new(self.resolve_expr(*expr)?);
        let args = args
            .into_iter()
            .map(|arg| self.resolve_expr(arg))
            .collect::<Result<_, _>>()?;

        Ok(Expression::Application(Application { expr, args }))
    }

    fn resolve_let(&mut self, Let { pattern, type_expr, expr, body }: Let) ->  ResolutionResult<Expression> {
        let expr = Box::new(self.resolve_expr(*expr)?);
        let type_expr = type_expr.map(|type_expr| self.resolve_type_expr(type_expr)).transpose()?;
        let local_count = self.push_names_in_pattern(&pattern);
        let body = Box::new(self.resolve_expr(*body)?);
        self.locals.truncate(self.locals.len() - local_count);

        Ok(Expression::Let(Let { pattern, type_expr, expr, body }))
    }

    fn resolve_lambda(&mut self, Lambda { params, body }: Lambda) -> ResolutionResult<Expression> {
        let local_count = params
            .iter()
            .map(|param| self.push_names_in_pattern(param))
            .sum::<usize>();
        let body = Box::new(self.resolve_expr(*body)?);
        self.locals.truncate(self.locals.len() - local_count);

        Ok(Expression::Lambda(Lambda { params, body }))
    }

    // TODO: Better error reporting here.
    fn resolve_access(&mut self, Access { path, .. }: Access) -> ResolutionResult<Expression> {
        let namespace = match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                if let Some(import) = self.names.imports.get(&from.data) {
                    import
                        .as_module()
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                        .0
                        .contains(&name.data)
                        .then_some(Namespace::Module)
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?

                } else if let Some(typ) = self.names.types.get(&from.data) {
                    typ
                        .contains(&name.data)
                        .then_some(Namespace::Type)
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                } else {
                    return Err(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))
                }
            },
            // In this case groups.len() >= 1 and they have to refer to a module group.
            [groups@.., from, name] => {
                let first = &groups.first().unwrap();
                let mut current_import = self.names.imports
                    .get(&first.data)
                    .ok_or(ResolutionError::NonExistantNamespace(first.data.clone()).attach(first.span))?;

                for module in &groups[1..] {
                    current_import = current_import
                        .as_group()
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                        .get(&module.data)
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?;
                }

                match current_import {
                    // If the current is a 'Module', before should be a 'Type' and we should access to a constructor.
                    ImportNames::Module { types, .. } => {
                        types.get(&from.data)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                            .contains(&name.data)
                            .then_some(Namespace::Type)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    }
                    // If the current is a 'Group', before should be a 'Module' and we should access to a function.
                    ImportNames::Group(modules) => {
                        modules.get(&from.data)
                            .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?
                            .as_module()
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                            .0
                            .contains(&name.data)
                            .then_some(Namespace::Module)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    }
                }
            },
        };

        Ok(Expression::Access(Access { path, namespace }))
    }

    fn resolve_type_expr(&mut self, type_expr: TypeExpression) -> ResolutionResult<TypeExpression> {
        match type_expr {
            TypeExpression::Identifier(identifier, _) => self.resolve_type_identifier(identifier),
            TypeExpression::Function(type_function) => self.resolve_type_function(type_function),
            TypeExpression::Access(path) => self.resolve_type_access(path),
        }
    }

    fn resolve_type_identifier(&self, identifier: Spanned<Symbol>) -> ResolutionResult<TypeExpression> {
        // TODO: Local type variables for polymorphic types.
        let bound = if self.names.types.contains_key(&identifier.data) {
            Bound::Global(identifier.data.clone())
        } else {
            return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
        };

        Ok(TypeExpression::Identifier(identifier, bound))
    }

    fn resolve_type_function(&mut self, TypeFunction { params, ret }: TypeFunction) -> ResolutionResult<TypeExpression> {
        let ret = Box::new(self.resolve_type_expr(*ret)?);
        let params = params
            .into_iter()
            .map(|arg| self.resolve_type_expr(arg))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TypeExpression::Function(TypeFunction { ret, params }))
    }

    fn resolve_type_access(&self, path: Vec<Spanned<Symbol>>) -> ResolutionResult<TypeExpression> {
        match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                self.names.imports
                    .get(&from.data)
                    .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?
                    .as_module()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .1
                    .contains_key(&name.data)
                    .then_some(())
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?;
            },
            // In this case modules.len() >= 1 and they have to refer to a module.
            [modules@.., from, name] => {
                let first = &modules.first().unwrap();
                let mut current_import = self.names.imports
                    .get(&first.data)
                    .ok_or(ResolutionError::NonExistantNamespace(first.data.clone()).attach(first.span))?;

                for module in &modules[1..] {
                    current_import = current_import
                        .as_group()
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                        .get(&module.data)
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?;
                }

                current_import
                    .as_group()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .get(&from.data)
                    .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?
                    .as_module()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .1
                    .contains_key(&name.data)
                    .then_some(())
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?;
            }
        }

        Ok(TypeExpression::Access(path))
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
        let ret = ret.map(|type_expr| self.resolve_type_expr(type_expr)).transpose()?;

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
        for (name, Import { parts, kind }) in imports {
            match kind {
                module::ImportKind::File(module) => {
                    let module = NameResolver::resolve_module(module).map_err(|error| {
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

                    let resolved_import = Import { parts, kind: module::ImportKind::File(module) };
                    resolved_imports.insert(name, resolved_import);
                },
                module::ImportKind::Folder(imports) => {
                    resolved_imports.insert(name, Import { parts, kind: module::ImportKind::Folder(Self::resolve_imports(imports)?)});
                },
            }
        }

        Ok(resolved_imports)
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

#[derive(Default)]
struct Names {
    functions: HashSet<Symbol>,
    imports: HashMap<Symbol, ImportNames>,
    types: HashMap<Symbol, HashSet<Symbol>>,
}

enum ImportNames {
    Module {
        functions: HashSet<Symbol>,
        types: HashMap<Symbol, HashSet<Symbol>>,
    },
    Group(HashMap<Symbol, ImportNames>)
}

impl ImportNames {
    fn as_group(&self) -> Option<&HashMap<Symbol, ImportNames>> {
        if let Self::Group(v) = self {
            Some(v)
        } else {
            None
        }
    }

    fn as_module(&self) -> Option<(&HashSet<Symbol>, &HashMap<Symbol, HashSet<Symbol>>)> {
        if let Self::Module { functions, types } = self {
            Some((functions, types))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum ResolutionError {
    UnboundIdentifier(Symbol),
    NonExistantNamespace(Symbol),
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
            Self::NonExistantNamespace(module) => write!(f, "Namespace `{module}` does not exist."),
            Self::UnboundInModule { module_name, name } => {
                write!(f, "`{name}` is not bound in module `{module_name}`.")
            }
            Self::ImportError { .. } => write!(f, "Error while importing module."),
        }
    }
}

impl HasSpan for ResolutionError {}

type ResolutionResult<T> = Result<T, Spanned<ResolutionError>>;

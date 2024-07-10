use std::{
    collections::{HashMap, HashSet}, fmt::Display
};

use crate::frontend::{
    span::{HasSpan, Spanned},
    token::Symbol,
};

use super::{
    ast::{Access, Application, Bound, Expression, TypeFunction, Let, Namespace, Pattern, TypeExpression},
    module::{self, Function, Import, Module}
};

pub struct NameResolver {
    names: Names,
    locals: Vec<Symbol>,
    module_path: Symbol
}

impl NameResolver {
    pub fn new(module: &Module, module_path: Symbol) -> Self {
        let mut resolver = Self {
            names: Names::default(),
            locals: Vec::new(),
            module_path,
        };

        resolver.collect_names(module);
        resolver
    }

    pub fn resolve_module(module: Module, module_path: Symbol) -> ResolutionResult<Module> {
        let mut resolver = Self::new(&module, module_path.clone());

        Ok(Module {
            functions: resolver.resolve_functions(module.functions)?,
            imports: resolver.resolve_imports(module.imports)?,
            types: resolver.resolve_types(module.types)?,
            path: module_path,
        })
    }

    fn collect_names(&mut self, module: &Module) {
        let types = module.types.iter().map(|(type_name, typ)| {
            (type_name.clone(), typ.consts.iter().map(|(name, _)| name.data.clone()).collect())
        }).collect();

        let functions = module.functions.keys().cloned().collect();


        let mut type_directs = HashMap::new();
        let mut func_directs = HashMap::new();
        let mut imports = HashMap::new();
        for (name, import) in &module.imports {
            let (names, import_type_directs, import_func_directs) = self.collect_import_names(import);
            type_directs.extend(import_type_directs);
            func_directs.extend(import_func_directs);
            imports.insert(name.clone(), names);
        }

        self.names = Names { functions, imports, types, type_directs, func_directs }
    }

    fn collect_import_names(&mut self, import: &Import) -> ((ImportNames, Vec<Symbol>), HashMap<Symbol, Vec<Symbol>>, HashMap<Symbol, Vec<Symbol>>) {
        match &import.kind {
            module::ImportKind::File((module, path)) => {
                let types: HashMap<_, _> = module.types.iter().map(|(type_name, typ)| {
                    (type_name.clone(), typ.consts.iter().map(|(name, _)| name.data.clone()).collect())
                }).collect();

                let functions: HashSet<_> = module.functions.keys().cloned().collect();

                let mut type_directs = HashMap::new();
                let mut func_directs = HashMap::new();
                for direct in &import.directs {
                    let mut path = vec![path.clone()];
                    path.push(direct.data.clone());

                    // NOTE: While importing Type has priority.
                    if types.contains_key(&direct.data) {
                        type_directs.insert(direct.data.clone(), path);
                    } else if functions.contains(&direct.data) {
                        func_directs.insert(direct.data.clone(), path);
                    } else {
                        todo!("Unbound name in module")
                    };
                }

                ((ImportNames::Module { functions, types }, vec![path.clone()]), type_directs, func_directs)
            },
            module::ImportKind::Folder((imports, path)) => {
                let mut modules = HashMap::new();
                for (name, import) in imports {
                    let (module, path) = self.collect_import_names(import).0;
                    modules.insert(name.clone(), (module, path));
                }

                // TODO: Direct importing namespaces
                ((ImportNames::Group(modules), vec![path.clone()]), HashMap::new(), HashMap::new())
            },
        }

    }

    pub fn resolve_expr(&mut self, expr: Expression) -> ResolutionResult<Expression> {
        match expr {
            Expression::Identifier(identifier, _) => self.resolve_identifier(identifier),
            Expression::Application(application) => self.resolve_application(application),
            Expression::Let(lett) => self.resolve_let(lett),
            Expression::Access(access) => self.resolve_access(access),
            literal => Ok(literal),
        }
    }

    fn resolve_identifier(&mut self, identifier: Spanned<Symbol>) -> ResolutionResult<Expression> {
        let bound = if let Some(indice) = self.locals.iter().rev().position(|local| local == &identifier.data) {
            Bound::Local(indice)
        } else if self.names.functions.contains(&identifier.data) {
            Bound::Absolute(self.make_path(identifier.data.clone()))
        } else if let Some(path) = self.names.func_directs.get(&identifier.data) {
            Bound::Absolute(path.clone())
        } else {
            return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
        };

        Ok(Expression::Identifier(identifier, bound))
    }

    fn make_path(&self, name: Symbol) -> Vec<Symbol> {
        if self.module_path.is_empty() {
            vec![name]
        } else {
            vec![self.module_path.clone(), name]
        }
    }

    fn resolve_application(&mut self, Application { expr, args }: Application) -> ResolutionResult<Expression> {
        let expr = Box::new(self.resolve_expr(*expr)?);
        let args = args
            .into_iter()
            .map(|arg| self.resolve_expr(arg))
            .collect::<Result<_, _>>()?;

        Ok(Expression::Application(Application { expr, args }))
    }

    fn resolve_let(&mut self, Let { expr, type_expr, branches }: Let) ->  ResolutionResult<Expression> {
        let expr = Box::new(self.resolve_expr(*expr)?);
        let type_expr = type_expr.map(|type_expr| self.resolve_type_expr(type_expr)).transpose()?;
        let mut resolved_branches = vec![];
        for (pattern, body) in branches {
            let pattern = self.resolve_pattern(pattern);
            let local_count = self.push_names_in_pattern(&pattern);
            let body = Box::new(self.resolve_expr(*body)?);
            self.locals.truncate(self.locals.len() - local_count);
            resolved_branches.push((pattern, body));
        }


        Ok(Expression::Let(Let { expr, type_expr, branches: resolved_branches }))
    }

    // TODO: Better error reporting here.
    fn resolve_access(&mut self, Access { path, .. }: Access) -> ResolutionResult<Expression> {
        let (namespace, mut import_path) = match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                if let Some((import, import_path)) = self.names.imports.get(&from.data) {
                    import
                        .as_module()
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                        .0
                        .contains(&name.data)
                        .then_some((Namespace::Module, import_path.clone()))
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?

                } else if let Some(typ) = self.names.types.get(&from.data) {
                    let path = self.make_path(from.data.clone());

                    typ
                        .contains(&name.data)
                        .then_some((Namespace::Type, path))
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
                    let a = &current_import.0;
                    current_import = a
                        .as_group()
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                        .get(&module.data)
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                }

                match &current_import.0 {
                    // If the current is a 'Module', before should be a 'Type' and we should access to a constructor.
                    ImportNames::Module { types, .. } => {
                        // HACK: trust me, we need to push here. just one more push, surely it will be fixed.
                        let mut path = current_import.1.clone();
                        path.push(from.data.clone());

                        types.get(&from.data)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                            .contains(&name.data)
                            .then_some((Namespace::Type, path))
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    }
                    // If the current is a 'Group', before should be a 'Module' and we should access to a function.
                    ImportNames::Group(modules) => {
                        let (module, path) = modules.get(&from.data)
                            .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?;

                        let path = path.clone();
                        // path.push(from.data.clone());

                        module
                            .as_module()
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                            .0
                            .contains(&name.data)
                            .then_some((Namespace::Module, path))
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    }
                }
            },
        };

        import_path.push(path.last().unwrap().data.clone());

        // let path2 = path.iter().map(|part| part.data.clone()).collect::<Vec<_>>();
        // dbg!(&path2);
        // dbg!(&import_path);
        // assert!(import_path.len() >= path2.len());

        Ok(Expression::Access(Access { path, namespace, real_path: import_path }))
    }

    fn resolve_type_expr(&mut self, type_expr: TypeExpression) -> ResolutionResult<TypeExpression> {
        match type_expr {
            TypeExpression::Identifier(identifier, _) => self.resolve_type_identifier(identifier),
            TypeExpression::Function(type_function) => self.resolve_type_function(type_function),
            TypeExpression::Access(path, _) => self.resolve_type_access(path),
        }
    }

    fn resolve_type_identifier(&self, identifier: Spanned<Symbol>) -> ResolutionResult<TypeExpression> {
        // TODO: Local type variables for polymorphic types.
        let bound = if self.names.types.contains_key(&identifier.data) {
            Bound::Absolute(self.make_path(identifier.data.clone()))
        } else if let Some(path) = self.names.type_directs.get(&identifier.data) {
            Bound::Absolute(path.clone())
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
        let mut real_path = match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                let (import, real_path) = self.names.imports
                    .get(&from.data)
                    .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?;

                import
                    .as_module()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .1
                    .contains_key(&name.data)
                    .then_some(real_path.clone())
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
            },
            // In this case modules.len() >= 1 and they have to refer to a module.
            [modules@.., from, name] => {
                let first = &modules.first().unwrap();
                let mut current_import = self.names.imports
                    .get(&first.data)
                    .ok_or(ResolutionError::NonExistantNamespace(first.data.clone()).attach(first.span))?;

                for module in &modules[1..] {
                    current_import = current_import.0
                        .as_group()
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                        .get(&module.data)
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?;
                }

                let (module, path) = current_import.0
                    .as_group()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .get(&from.data)
                    .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?;

                module
                    .as_module()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .1
                    .contains_key(&name.data)
                    .then_some(path.clone())
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
            }
        };

        real_path.push(path.last().unwrap().data.clone());
        Ok(TypeExpression::Access(path, real_path))
    }

    fn resolve_function(&mut self, Function { name, params, ret, branches }: Function) -> ResolutionResult<Function> {
        let params = params.into_iter().map(|param| self.resolve_type_expr(param)).collect::<Result<Vec<_>, _>>()?;

        let mut resolved_branches = vec![];
        for (patterns, body) in branches {
            let mut local_count = 0;
            let patterns = patterns
                .into_iter()
                .map(|pattern| self.resolve_pattern(pattern))
                .collect::<Vec<_>>();

            for pattern in &patterns {
                local_count += self.push_names_in_pattern(pattern);
            }

            let body = self.resolve_expr(body)?;
            self.locals.truncate(self.locals.len() - local_count);
            resolved_branches.push((patterns, body));
            assert!(self.locals.is_empty());
        }

        let ret = ret.map(|type_expr| self.resolve_type_expr(type_expr)).transpose()?;

        Ok(Function { name, params, ret, branches: resolved_branches })
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

    fn resolve_import(&mut self, Import { parts, kind, directs }: Import) -> ResolutionResult<Import> {
        match kind {
            module::ImportKind::File((module, path)) => {
                // dbg!(&path);

                let module = NameResolver::resolve_module(module, path.clone()).map_err(|error| {
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

                Ok(Import { parts, kind: module::ImportKind::File((module, path)), directs })
            },
            module::ImportKind::Folder((imports, path)) => {
                let mut modules = HashMap::new();
                for (name, import) in imports {
                    modules.insert(name, self.resolve_import(import)?);
                }

                Ok(Import {
                    parts,
                    kind: module::ImportKind::Folder((self.resolve_imports(modules)?, path)),
                    directs
                })
            },
        }
    }

    fn resolve_imports(&mut self, imports: HashMap<Symbol, Import>) -> ResolutionResult<HashMap<Symbol, Import>> {
        let mut resolved_imports = HashMap::new();

        for (name, import) in imports {
            resolved_imports.insert(name, self.resolve_import(import)?);
        }

        Ok(resolved_imports)
    }

    fn resolve_pattern(&mut self, pattern: Pattern) -> Pattern {
        match pattern {
            Pattern::Constructor { path, params, real_path: _ } => {
                // TODO: Remove unwrap.
                let Expression::Access(Access { path, namespace, real_path }) =
                    self.resolve_access(Access { path: path.to_vec(), namespace: Namespace::Type, real_path: vec![] }).unwrap() else {
                    unreachable!()
                };

                assert!(namespace == Namespace::Type);

                let params = params.into_iter().map(|param| self.resolve_pattern(param)).collect();
                Pattern::Constructor { path, real_path, params }
            },
            literal => literal
        }
    }

    fn push_names_in_pattern(&mut self, pattern: &Pattern) -> usize {
        match pattern {
            Pattern::Any(identifier) => {
                self.locals.push(identifier.data.clone());
                1
            }
            Pattern::Constructor { path: _, params, real_path: _ } => {
                let mut local_count = 0;
                for param in params {
                    local_count += self.push_names_in_pattern(param);
                }

                local_count
            },
            Pattern::String(_) | Pattern::Float(_) | Pattern::Integer(_) => 0,
        }
    }
}

#[derive(Default)]
struct Names {
    functions: HashSet<Symbol>,
    imports: HashMap<Symbol, (ImportNames, Vec<Symbol>)>,
    types: HashMap<Symbol, HashSet<Symbol>>,
    type_directs: HashMap<Symbol, Vec<Symbol>>,
    func_directs: HashMap<Symbol, Vec<Symbol>>,
}

enum ImportNames {
    Module {
        functions: HashSet<Symbol>,
        types: HashMap<Symbol, HashSet<Symbol>>,
    },
    Group(HashMap<Symbol, (ImportNames, Vec<Symbol>)>)
}

impl ImportNames {
    fn as_group(&self) -> Option<&HashMap<Symbol, (ImportNames, Vec<Symbol>)>> {
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

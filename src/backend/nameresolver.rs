use std::{
    collections::{HashMap, HashSet}, fmt::Display
};

use crate::frontend::{
    span::{HasSpan, Spanned},
    token::Symbol,
};

use super::{
    ast::{AbsoluteBound, Access, Application, Bound, ConstructorBound, Direct, Expression, Let, ModuleBound, Pattern, TypeExpression, TypeFunction},
    module::{self, Function, Import, Module}
};

pub struct NameResolver {
    names: Names,
    locals: Vec<Symbol>,
    type_locals: Vec<Symbol>,
    module_path: Symbol
}

impl NameResolver {
    pub fn new(module: &Module) -> Self {
        Self {
            names: Self::collect_names(module),
            locals: Vec::new(),
            type_locals: Vec::new(),
            module_path: module.path.clone(),
        }
    }

    pub fn resolve_module(module: Module) -> ResolutionResult<Module> {
        let mut resolver = Self::new(&module);

        Ok(Module {
            functions: resolver.resolve_functions(module.functions)?,
            imports: resolver.resolve_imports(module.imports)?,
            types: resolver.resolve_types(module.types)?,
            path: module.path,
        })
    }

    fn collect_names(module: &Module) -> Names {
        let functions = Self::collect_function_names(&module.functions);
        let types = Self::collect_type_names(&module.types);
        let (modules, type_directs, function_directs) = Self::collect_module_names_and_directs(&module.imports);

        Names { functions, modules, types, type_directs, function_directs }
    }

    fn collect_function_names(functions: &HashMap<Symbol, Function>) -> FunctionNames {
        functions.keys().cloned().collect()
    }

    fn collect_type_names(types: &HashMap<Symbol, module::Type>) -> TypeNames {
        types.iter().map(|(type_name, typ)| {
            (type_name.clone(), typ.consts.iter().map(|(name, _)| name.data.clone()).collect())
        }).collect()
    }

    fn collect_module_names_and_directs(imports: &HashMap<Symbol, Import>) -> (ModuleNames, TypeDirects, FunctionDirects) {
        let mut type_directs = HashMap::new();
        let mut function_directs = HashMap::new();
        let mut modules = HashMap::new();
        for (name, import) in imports {
            let (import_names, (import_type_directs, import_function_directs, import_module_directs)) =
                Self::collect_import_names_and_directs(import);

            type_directs.extend(import_type_directs);
            function_directs.extend(import_function_directs);
            modules.insert(name.clone(), import_names);
            modules.extend(import_module_directs);
        }

        (modules, type_directs, function_directs)
    }

    fn collect_import_names_and_directs(import: &Import) -> ((ImportNames, Symbol), ImportDirects) {
        match &import.kind {
            module::ImportKind::File(module) => {
                let functions = Self::collect_function_names(&module.functions);
                let types = Self::collect_type_names(&module.types);

                let (type_directs, function_directs) =
                    Self::resolve_module_directs(&functions, &types, &import.directs, &module.path).unwrap();

                ((ImportNames::Module(functions, types), module.path.clone()), (type_directs, function_directs, HashMap::default()))
            },
            module::ImportKind::Folder((imports, path)) => {
                let modules = imports.iter().map(|(name, import)| {
                    (name.clone(), Self::collect_import_names_and_directs(import).0)
                }).collect();

                let import_directs = Self::resolve_group_directs(&modules, &import.directs).unwrap();

                ((ImportNames::Group(modules), path.clone()), import_directs)
            },
        }

    }

    pub fn resolve_expr(&mut self, expr: Expression) -> ResolutionResult<Expression> {
        match expr {
            Expression::Identifier(identifier, _) => self.resolve_identifier(identifier),
            Expression::Application(application) => self.resolve_application(application),
            Expression::Let(lett) => self.resolve_let(lett),
            Expression::Access(access) => self.resolve_access(access.path),
            literal => Ok(literal),
        }
    }

    fn resolve_identifier(&mut self, identifier: Spanned<Symbol>) -> ResolutionResult<Expression> {
        let bound = if let Some(indice) = self.locals.iter().rev().position(|local| local == &identifier.data) {
            Bound::Local(indice)
        } else if self.names.functions.contains(&identifier.data) {
            Bound::Absolute(AbsoluteBound::Module(ModuleBound { module: self.module_path.clone(), name: identifier.data.clone() }))
        } else if let Some(abs_bound) = self.names.function_directs.get(&identifier.data) {
            Bound::Absolute(abs_bound.clone())
        } else {
            return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
        };

        Ok(Expression::Identifier(identifier, bound))
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
            let local_count = self.push_pattern_locals(&pattern);
            let body = Box::new(self.resolve_expr(*body)?);
            self.locals.truncate(self.locals.len() - local_count);
            resolved_branches.push((pattern, body));
        }

        Ok(Expression::Let(Let { expr, type_expr, branches: resolved_branches }))
    }

    fn resolve_module_directs(functions: &FunctionNames, types: &TypeNames, directs: &[Direct], module_path: &Symbol)
        -> ResolutionResult<(TypeDirects, FunctionDirects)>
    {
        let mut function_directs = HashMap::new();
        let mut type_directs = HashMap::new();

        for Direct { parts, directs } in directs {
            match &parts[..] {
                [name] => {
                    let bound = ModuleBound { module: module_path.clone(), name: name.data.clone() };

                    // NOTE: While importing Type has priority.
                    if let Some(constructors) = types.get(&name.data) {
                        type_directs.insert(name.data.clone(), (constructors.clone(), bound));
                        function_directs.extend(Self::resolve_type_directs(directs, constructors, module_path, name)?);
                    } else if functions.contains(&name.data) {
                        function_directs.insert(name.data.clone(), AbsoluteBound::Module(bound));

                        if !directs.is_empty() {
                            todo!("Unbound name in module")
                        }

                    } else {
                        todo!("Unbound name in module")
                    };
                },
                _ => todo!("Unbound name in module"),
            };
        }

        Ok((type_directs, function_directs))
    }

    fn resolve_group_directs(modules: &ModuleNames, directs: &Vec<Direct>) -> ResolutionResult<ImportDirects> {
        let mut function_directs = HashMap::new();
        let mut module_directs = HashMap::new();
        let mut type_directs = HashMap::new();

        for Direct { parts, directs } in directs {
            match &parts[..] {
                [name] => {
                    let Some((names, path)) = modules.get(&name.data) else {
                        todo!("Unbound module")
                    };

                    match names {
                        ImportNames::Module(functions, types) => {
                            let (module_type_directs, module_function_directs) =
                                Self::resolve_module_directs(functions, types, directs, path).unwrap();

                            function_directs.extend(module_function_directs);
                            type_directs.extend(module_type_directs);
                        },
                        ImportNames::Group(modules) => {
                            let (group_type_directs, group_function_directs, group_module_directs) =
                                Self::resolve_group_directs(modules, directs).unwrap();

                            function_directs.extend(group_function_directs);
                            type_directs.extend(group_type_directs);
                            module_directs.extend(group_module_directs);
                        },
                    };

                    module_directs.insert(name.data.clone(), (names.clone(), path.clone()));
                },
                // In this case groups.len() >= 1 and they have to refer to a module group.
                [groups@.., name] => {
                    let first = &groups.first().unwrap();
                    let mut current_import = modules
                        .get(&first.data)
                        .ok_or(ResolutionError::NonExistantNamespace(first.data.clone()).attach(first.span))?;

                    for module in &groups[1..] {
                        let a = &current_import.0;
                        current_import = a
                            .as_group()
                            .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                            .get(&module.data)
                            .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?;
                    }

                    match &current_import.0 {
                        ImportNames::Module(_functions, types) => {
                            let bound = ModuleBound {
                                module: current_import.1.clone(),
                                name: name.data.clone()
                            };

                            let constructors = types.get(&name.data)
                                .ok_or(ResolutionError::UnboundInModule { module_name: groups.last().unwrap().data.clone(), name: name.data.clone() }.attach(name.span))?;

                            type_directs.insert(name.data.clone(), (constructors.clone(), bound));
                            function_directs.extend(Self::resolve_type_directs(directs, constructors, &current_import.1, name)?);
                        }
                        ImportNames::Group(modules) => {
                            let (names, path) = modules.get(&name.data).expect("unbound");

                            match names {
                                ImportNames::Module(functions, types) => {
                                    let (module_type_directs, module_function_directs) =
                                        Self::resolve_module_directs(functions, types, directs, path).unwrap();

                                    function_directs.extend(module_function_directs);
                                    type_directs.extend(module_type_directs);
                                },
                                ImportNames::Group(modules) => {
                                    let (group_type_directs, group_function_directs, group_module_directs) =
                                        Self::resolve_group_directs(modules, directs).unwrap();

                                    function_directs.extend(group_function_directs);
                                    type_directs.extend(group_type_directs);
                                    module_directs.extend(group_module_directs);
                                },
                            };

                            module_directs.insert(name.data.clone(), (names.clone(), path.clone()));
                        }
                    }
                },
                _ => todo!("Unbound name in module"),
            }
        }

        Ok((type_directs, function_directs, module_directs))
    }

    fn resolve_type_directs(directs: &[Direct], constructors: &FunctionNames, module_path: &Symbol, type_name: &Spanned<Symbol>)
        -> ResolutionResult<FunctionDirects>
    {
        let mut function_directs = HashMap::new();
        for Direct { parts, directs } in directs {
            if !directs.is_empty() {
                todo!("Unbound name in module")
            }

            match &parts[..] {
                [constructor_name] => {
                    let bound = AbsoluteBound::Constructor(ConstructorBound {
                        module: module_path.clone(),
                        typ: type_name.data.clone(),
                        name: constructor_name.data.clone()
                    });

                    constructors
                        .contains(&constructor_name.data)
                        .then_some(())
                        .ok_or(ResolutionError::UnboundInModule { module_name: type_name.data.clone(), name: constructor_name.data.clone() }.attach(type_name.span))?;

                    function_directs.insert(constructor_name.data.clone(), bound);
                },
                _ => todo!("Unbound name in module"),
            }
        }

        Ok(function_directs)
    }

    // TODO: Better error reporting here.
    fn resolve_access(&mut self, path: Vec<Spanned<Symbol>>) -> ResolutionResult<Expression> {
        let abs_bound = match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                if let Some((import, import_path)) = self.names.modules.get(&from.data) {
                    let bound = AbsoluteBound::Module(ModuleBound {
                        module: import_path.clone(),
                        name: name.data.clone()
                    });

                    import
                        .as_module()
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                        .0
                        .contains(&name.data)
                        .then_some(bound)
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?

                } else if let Some(typ) = self.names.types.get(&from.data) {
                    let bound = AbsoluteBound::Constructor(ConstructorBound {
                        module: self.module_path.clone(),
                        typ: from.data.clone(),
                        name: name.data.clone()
                    });

                    typ
                        .contains(&name.data)
                        .then_some(bound)
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                } else if let Some((typ, path)) = self.names.type_directs.get(&from.data) {
                    let ModuleBound { module, name: type_name } = path;

                    let bound = AbsoluteBound::Constructor(ConstructorBound {
                        module: module.clone(),
                        typ: type_name.clone(),
                        name: name.data.clone()
                    });

                    typ
                        .contains(&name.data)
                        .then_some(bound)
                        .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                } else {
                    return Err(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))
                }
            },
            // In this case groups.len() >= 1 and they have to refer to a module group.
            [groups@.., from, name] => {
                let first = &groups.first().unwrap();
                let mut current_import = self.names.modules
                    .get(&first.data)
                    .ok_or(ResolutionError::NonExistantNamespace(first.data.clone()).attach(first.span))?;

                for module in &groups[1..] {
                    let a = &current_import.0;
                    current_import = a
                        .as_group()
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?
                        .get(&module.data)
                        .ok_or(ResolutionError::NonExistantNamespace(module.data.clone()).attach(module.span))?;
                }

                match &current_import.0 {
                    // If the current is a 'Module', before should be a 'Type' and we should access to a constructor.
                    ImportNames::Module(_functions, types) => {
                        let bound = AbsoluteBound::Constructor(ConstructorBound {
                            module: current_import.1.clone(),
                            typ: from.data.clone(),
                            name: name.data.clone()
                        });

                        types.get(&from.data)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                            .contains(&name.data)
                            .then_some(bound)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    }
                    // If the current is a 'Group', before should be a 'Module' and we should access to a function.
                    ImportNames::Group(modules) => {
                        let (module, path) = modules.get(&from.data)
                            .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?;

                        let bound = AbsoluteBound::Module(ModuleBound {
                            module: path.clone(),
                            name: name.data.clone()
                        });

                        module
                            .as_module()
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                            .0
                            .contains(&name.data)
                            .then_some(bound)
                            .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    }
                }
            },
        };

        Ok(Expression::Access(Access { path, abs_bound }))
    }

    fn resolve_type_expr(&mut self, type_expr: TypeExpression) -> ResolutionResult<TypeExpression> {
        match type_expr {
            TypeExpression::Identifier(identifier, _, args) => self.resolve_type_identifier(identifier, args),
            TypeExpression::Function(type_function) => self.resolve_type_function(type_function),
            TypeExpression::Access(path, _, args) => self.resolve_type_access(path, args),
        }
    }

    fn resolve_type_identifier(&mut self, identifier: Spanned<Symbol>, args: Option<Vec<TypeExpression>>) -> ResolutionResult<TypeExpression> {
        let bound = if let Some(indice) = self.type_locals.iter().rev().position(|local| local == &identifier.data) {
            Bound::Local(indice)
        } else if self.names.types.contains_key(&identifier.data) {
            Bound::Absolute(AbsoluteBound::Module(ModuleBound { module: self.module_path.clone(), name: identifier.data.clone() }))
        } else if let Some((_, bound)) = self.names.type_directs.get(&identifier.data) {
            Bound::Absolute(AbsoluteBound::Module(bound.clone()))
        } else {
            return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
        };

        let args = if let Some(args) = args {
            let mut resolved_args = vec![];
            for arg in args {
                resolved_args.push(self.resolve_type_expr(arg)?)
            }
            Some(resolved_args)
        } else {
            None
        };

        Ok(TypeExpression::Identifier(identifier, bound, args))
    }

    fn resolve_type_function(&mut self, TypeFunction { params, ret }: TypeFunction) -> ResolutionResult<TypeExpression> {
        let ret = Box::new(self.resolve_type_expr(*ret)?);
        let params = params
            .into_iter()
            .map(|arg| self.resolve_type_expr(arg))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TypeExpression::Function(TypeFunction { ret, params }))
    }

    fn resolve_type_access(&mut self, path: Vec<Spanned<Symbol>>, args: Option<Vec<TypeExpression>>) -> ResolutionResult<TypeExpression> {
        let bound = match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                let (import, real_path) = self.names.modules
                    .get(&from.data)
                    .ok_or(ResolutionError::NonExistantNamespace(from.data.clone()).attach(from.span))?;

                let bound = AbsoluteBound::Module(ModuleBound {
                    module: real_path.clone(),
                    name: name.data.clone()
                });

                import
                    .as_module()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .1
                    .contains_key(&name.data)
                    .then_some(bound)
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
            },
            // In this case modules.len() >= 1 and they have to refer to a module.
            [modules@.., from, name] => {
                let first = &modules.first().unwrap();
                let mut current_import = self.names.modules
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

                let bound = AbsoluteBound::Module(ModuleBound {
                    module: path.clone(),
                    name: name.data.clone()
                });

                module
                    .as_module()
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
                    .1
                    .contains_key(&name.data)
                    .then_some(bound)
                    .ok_or(ResolutionError::UnboundInModule { module_name: from.data.clone(), name: name.data.clone() }.attach(name.span))?
            }
        };

        let args = if let Some(args) = args {
            let mut resolved_args = vec![];
            for arg in args {
                resolved_args.push(self.resolve_type_expr(arg)?)
            }
            Some(resolved_args)
        } else {
            None
        };

        Ok(TypeExpression::Access(path, bound, args))
    }

    fn resolve_function(&mut self, Function { name, params, ret, branches }: Function) -> ResolutionResult<Function> {
        let params = params
            .into_iter()
            .map(|param| self.resolve_type_expr(param))
            .collect::<Result<Vec<_>, _>>()?;

        let mut resolved_branches = vec![];
        for (patterns, body) in branches {
            let patterns = patterns
                .into_iter()
                .map(|pattern| self.resolve_pattern(pattern))
                .collect::<Vec<_>>();

            let local_count = patterns
                .iter()
                .map(|pattern| self.push_pattern_locals(pattern))
                .sum::<usize>();

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
        for (type_name, module::Type { type_vars, name, consts }) in types {
            if let Some(type_vars) = type_vars.as_ref() {
                for type_var in type_vars {
                    self.type_locals.push(type_var.data.clone())
                }
            }

            let mut resolved_constructors = vec![];
            for (name, params) in consts {
                let params = params
                    .into_iter()
                    .map(|param| self.resolve_type_expr(param))
                    .collect::<Result<Vec<_>, _>>()?;
                resolved_constructors.push((name, params));
            }

            self.locals.truncate(self.type_locals.len() - type_vars.as_ref().map(|t| t.len()).unwrap_or(0));
            resolved_types.insert(type_name, module::Type { type_vars, name, consts: resolved_constructors });
        }

        Ok(resolved_types)
    }

    fn resolve_import(&mut self, Import { parts, kind, directs }: Import) -> ResolutionResult<Import> {
        let kind = match kind {
            module::ImportKind::File(module) => {
                let import_path = module.path.clone().into();
                let module = NameResolver::resolve_module(module).map_err(|error| {
                    let first = parts.first().unwrap().span;
                    let last = parts.last().unwrap().span;
                    let span = first.extend(last);
                    ResolutionError::ImportError {
                        import_path,
                        error: Box::new(error),
                    }
                    .attach(span)
                })?;

                module::ImportKind::File(module)
            },
            module::ImportKind::Folder((imports, path)) => {
                module::ImportKind::Folder((self.resolve_imports(imports)?, path))
            },
        };

        Ok(Import { parts, kind, directs })
    }

    fn resolve_imports(&mut self, imports: HashMap<Symbol, Import>) -> ResolutionResult<HashMap<Symbol, Import>> {
        let mut resolved_imports = HashMap::with_capacity(imports.len());
        for (name, import) in imports {
            resolved_imports.insert(name, self.resolve_import(import)?);
        }

        Ok(resolved_imports)
    }

    fn resolve_pattern(&mut self, pattern: Pattern) -> Pattern {
        match pattern {
            Pattern::Constructor { path, params, abs_bound: _ } => {
                let abs_bound = match &path[..] {
                    [name] => {
                        // TODO: Remove unwrap.
                        let Expression::Identifier(_, Bound::Absolute(abs_bound)) = self.resolve_identifier(name.clone()).unwrap() else {
                            unreachable!()
                        };

                        abs_bound
                    },
                    _ => {
                        // TODO: Remove unwrap.
                        let Expression::Access(Access { path: _, abs_bound }) = self.resolve_access(path.clone()).unwrap() else {
                            unreachable!()
                        };

                        abs_bound
                    }
                };

                assert!(matches!(abs_bound, AbsoluteBound::Constructor { .. }));

                let params = params
                    .into_iter()
                    .map(|param| self.resolve_pattern(param))
                    .collect();

                Pattern::Constructor { path, abs_bound, params }
            },
            literal => literal
        }
    }

    fn push_pattern_locals(&mut self, pattern: &Pattern) -> usize {
        match pattern {
            Pattern::Any(identifier) => {
                self.locals.push(identifier.data.clone());
                1
            }
            Pattern::Constructor { params, .. } => {
                params.iter().map(|param| self.push_pattern_locals(param)).sum()
            },
            Pattern::String(_)
            | Pattern::Float(_)
            | Pattern::Integer(_) => 0,
        }
    }
}

type FunctionNames = HashSet<Symbol>;
type TypeNames = HashMap<Symbol, FunctionNames>;
type ModuleNames = HashMap<Symbol, (ImportNames, Symbol)>;

type TypeDirects = HashMap<Symbol, (FunctionNames, ModuleBound)>;
type FunctionDirects = HashMap<Symbol, AbsoluteBound>;
type ImportDirects = (TypeDirects, FunctionDirects, ModuleNames);

struct Names {
    functions: FunctionNames,
    modules: ModuleNames,
    types: TypeNames,
    type_directs: TypeDirects,
    function_directs: FunctionDirects,
}

#[derive(Clone)]
enum ImportNames {
    Module(FunctionNames, TypeNames),
    Group(ModuleNames)
}

impl ImportNames {
    fn as_module(&self) -> Option<(&FunctionNames, &TypeNames)> {
        if let Self::Module(functions, types) = self {
            Some((functions, types))
        } else {
            None
        }
    }

    fn as_group(&self) -> Option<&ModuleNames> {
        if let Self::Group(v) = self {
            Some(v)
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

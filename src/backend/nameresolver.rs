use std::{
    collections::HashMap,
    fmt::Display,
};

use crate::frontend::{
    span::{HasSpan, Spanned},
    token::Symbol,
};

use super::{ast::{Bound, Expression, Pattern, TypeExpr, TypedPattern}, module::{self, Function, Import, Module}};

pub struct NameResolver {
    module: Module,
    locals: Vec<Symbol>,
}

impl NameResolver {
    pub fn new() -> Self {
        let primitive_types: HashMap<Symbol, module::Type> = HashMap::from([
            ("Integer".into(), module::Type {}),
            ("String".into(), module::Type {}),
            ("Float".into(), module::Type {}),
            ("Nothing".into(), module::Type {}),
        ]);

        Self {
            module: Module { types: primitive_types, ..Default::default() },
            locals: Vec::new(),
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
                    let Some(_) = self.module.functions.get(&identifier.data) else {
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
            Expression::Access { module_name, name } => {
                let Some(import) = self.module.imports.get(&module_name.data) else {
                    return Err(ResolutionError::NonExistantModule(module_name.data).attach(module_name.span))
                };

                let Some(_) = import.module.functions.get(&name.data) else {
                    let span = module_name.span.extend(name.span);
                    return Err(ResolutionError::UnboundInModule { module_name: module_name.data, name: name.data }.attach(span))
                };

                Expression::Access { module_name, name }
            }
        };

        Ok(resolved_expr)
    }

    fn resolve_type_expr(&mut self, type_expr: TypeExpr) -> ResolutionResult<TypeExpr> {
        let resolved_type_expr = match type_expr {
            // TODO: Local type variables for polyphormic types.
            TypeExpr::Identifier(identifier, _) => {
                let Some(_) = self.module.types.get(&identifier.data) else {
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

    fn resolve_imports(&self, imports: HashMap<Symbol, Import>) -> ResolutionResult<HashMap<Symbol, Import>> {
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
        self.module.imports = self.resolve_imports(module.imports)?;
        // TODO: here resolve_types order is important.
        self.module.functions = self.resolve_functions(module.functions)?;

        Ok(self.module)
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

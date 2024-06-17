use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::frontend::span::{HasSpan, Spanned};

use super::ast::{Bound, Declaration, Expression, Module, Pattern};

pub struct NameResolver<'source> {
    locals: Vec<&'source str>,
    globals: HashSet<&'source str>,
    imports: HashMap<&'source str, Module<'source>>,
}

impl<'source> NameResolver<'source> {
    pub fn new() -> Self {
        Self {
            locals: Vec::new(),
            globals: HashSet::new(),
            imports: HashMap::new(),
        }
    }

    pub fn resolve_names_in_expr(
        &mut self,
        expr: Spanned<'source, Expression<'source>>,
    ) -> ResolutionResult<'source, Expression<'source>> {
        let resolved_expr = match expr.data {
            Expression::Integer(_) | Expression::Float(_) | Expression::String(_) => expr.data,
            Expression::Identifier(identifier, _) => {
                if let Some(indice) = self
                    .locals
                    .iter()
                    .rev()
                    .position(|local| local == &identifier)
                {
                    Expression::Identifier(identifier, Bound::Local(indice))
                } else {
                    let name = self
                        .globals
                        .get(identifier)
                        .ok_or(ResolutionError::UnboundIdentifier(identifier).attach(expr.span))?;

                    Expression::Identifier(identifier, Bound::Global(name))
                }
            }
            Expression::Binary { lhs, op, rhs } => Expression::Binary {
                lhs: Box::new(self.resolve_names_in_expr(*lhs)?),
                op,
                rhs: Box::new(self.resolve_names_in_expr(*rhs)?),
            },
            Expression::Application { expr, args } => Expression::Application {
                expr: Box::new(self.resolve_names_in_expr(*expr)?),
                args: args
                    .into_iter()
                    .map(|arg| self.resolve_names_in_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Expression::Let {
                pattern,
                expr,
                body,
            } => {
                let expr = self.resolve_names_in_expr(*expr)?;
                let local_count = self.push_names_in_pattern(&pattern);
                let body = self.resolve_names_in_expr(*body)?;
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Let {
                    pattern,
                    expr: Box::new(expr),
                    body: Box::new(body),
                }
            }
            Expression::Lambda { params, body } => {
                let local_count: usize = params
                    .iter()
                    .map(|param| self.push_names_in_pattern(param))
                    .sum();
                let body = self.resolve_names_in_expr(*body)?;
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Lambda {
                    params,
                    body: Box::new(body),
                }
            }
            Expression::Access { module_name, name } => {
                let Some(module) = self.imports.get(module_name.data) else {
                    return Err(ResolutionError::NonExistantModule(module_name.data).attach(module_name.span))
                };
                let Some(_) = module.decls.get(name.data) else {
                    return Err(ResolutionError::UnboundInModule { module_name: module_name.data, name: name.data }.attach(name.span))
                };

                Expression::Access { module_name, name }
            }
        };

        Ok(resolved_expr.attach(expr.span))
    }

    fn resolve_names_in_declaration(
        &mut self,
        decl: Spanned<'source, Declaration<'source>>,
    ) -> ResolutionResult<'source, Declaration<'source>> {
        let resolved_decl = match decl.data {
            Declaration::Function { name, params, body } => {
                let local_count: usize = params
                    .iter()
                    .map(|param| self.push_names_in_pattern(param))
                    .sum();
                let body = self.resolve_names_in_expr(body)?;
                self.locals.truncate(self.locals.len() - local_count);

                Declaration::Function { name, params, body }
            }
            Declaration::Import { parts: _ } => decl.data,
        };

        Ok(resolved_decl.attach(decl.span))
    }

    fn collect_declarations(&mut self, module: &Module<'source>) {
        for decl in module.decls.values() {
            #[allow(clippy::single_match)]
            match &decl.data {
                Declaration::Function { name, .. } => {
                    // TODO: Handle duplicate function declarations
                    self.globals.insert(name.data);
                }
                _ => (),
            }
        }
    }

    fn handle_imports(
        &mut self,
        imports: HashMap<&'source str, Module<'source>>,
    ) -> Result<(), Spanned<'source, ResolutionError<'source>>> {
        for (name, module) in imports {
            let resolved_module = NameResolver::new().resolve_names_in_module(module)?;
            self.imports.insert(name, resolved_module);
        }

        Ok(())
    }

    pub fn resolve_names_in_module(
        mut self,
        module: Module<'source>,
    ) -> Result<Module<'source>, Spanned<'source, ResolutionError<'source>>> {
        self.collect_declarations(&module);
        self.handle_imports(module.imports)?;

        let mut resolved_module = HashMap::new();
        for (name, decl) in module.decls {
            let resolved_decl = self.resolve_names_in_declaration(decl)?;
            resolved_module.insert(name, resolved_decl);
        }

        Ok(Module::new(resolved_module, self.imports))
    }

    fn push_names_in_pattern(&mut self, pattern: &Spanned<'source, Pattern<'source>>) -> usize {
        match pattern.data {
            Pattern::Any(identifier) => {
                self.locals.push(identifier);
                1
            }
            _ => 0,
        }
    }
}

pub enum ResolutionError<'source> {
    UnboundIdentifier(&'source str),
    NonExistantModule(&'source str),
    UnboundInModule {
        module_name: &'source str,
        name: &'source str,
    },
}

impl Display for ResolutionError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundIdentifier(identifier) => write!(f, "`{identifier}` is not bound."),
            Self::NonExistantModule(module) => write!(f, "Module `{module}` does not exist."),
            Self::UnboundInModule { module_name, name } => {
                write!(f, "`{name}` is not bound in module `{module_name}`.")
            }
        }
    }
}

impl HasSpan for ResolutionError<'_> {}

type ResolutionResult<'a, T> = Result<Spanned<'a, T>, Spanned<'a, ResolutionError<'a>>>;

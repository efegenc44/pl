use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::frontend::{
    span::{HasSpan, Spanned},
    token::Symbol,
};

use super::ast::{Bound, Declaration, Expression, Import, Module, Pattern, TypeExpr, TypedPattern};

pub struct NameResolver {
    locals: Vec<Symbol>,
    decls: HashSet<Symbol>,
    imports: HashMap<Symbol, Import>,
    types: HashSet<Symbol>,
}

impl NameResolver {
    pub fn new() -> Self {
        let primtive_types: [Box<str>; 4] = [
            "Integer".into(),
            "String".into(),
            "Float".into(),
            "Nothing".into()
        ];

        Self {
            locals: Vec::new(),
            decls: HashSet::new(),
            imports: HashMap::new(),
            types: HashSet::from(primtive_types),
        }
    }

    pub fn resolve_names_in_expr(&mut self, expr: Expression) -> ResolutionResult<Expression> {
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
                    let Some(name) = self.decls.get(&identifier.data) else {
                        return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
                    };

                    Expression::Identifier(identifier, Bound::Global(name.clone()))
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
            Expression::Let { pattern, typ, expr, body } => {
                let expr = Box::new(self.resolve_names_in_expr(*expr)?);
                let typ = if let Some(typ) = typ {
                    Some(self.resolve_names_in_type_expr(typ)?)
                } else {
                    None
                };
                let local_count = self.push_names_in_pattern(&pattern);
                let body = Box::new(self.resolve_names_in_expr(*body)?);
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Let { pattern, typ, expr, body }
            }
            Expression::Lambda { params, body } => {
                let local_count = params
                    .iter()
                    .map(|param| self.push_names_in_pattern(param))
                    .sum::<usize>();
                let body = Box::new(self.resolve_names_in_expr(*body)?);
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Lambda { params, body }
            }
            Expression::Access { module_name, name } => {
                let Some(import) = self.imports.get(&module_name.data) else {
                    return Err(ResolutionError::NonExistantModule(module_name.data).attach(module_name.span))
                };

                let Some(_) = import.module.decls.get(&name.data) else {
                    let span = module_name.span.extend(name.span);
                    return Err(ResolutionError::UnboundInModule { module_name: module_name.data, name: name.data }.attach(span))
                };

                Expression::Access { module_name, name }
            }
        };

        Ok(resolved_expr)
    }

    fn resolve_names_in_type_expr(&mut self, type_expr: TypeExpr) -> ResolutionResult<TypeExpr> {
        let resolved_type_expr = match type_expr {
            // TODO: Local type variables for polyphormic types.
            TypeExpr::Identifier(identifier, _) => {
                let Some(name) = self.types.get(&identifier.data) else {
                    return Err(ResolutionError::UnboundIdentifier(identifier.data.clone()).attach(identifier.span))
                };

                TypeExpr::Identifier(identifier, Bound::Global(name.clone()))
            }
            TypeExpr::Function { params, ret } => TypeExpr::Function {
                ret: Box::new(self.resolve_names_in_type_expr(*ret)?),
                params: params
                    .into_iter()
                    .map(|arg| self.resolve_names_in_type_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            },
        };

        Ok(resolved_type_expr)
    }

    fn resolve_names_in_decl(&mut self, decl: Declaration) -> ResolutionResult<Declaration> {
        let resolved_decl = match decl {
            Declaration::Function { name, params, body, ret } => {
                let mut resolved_params = vec![];
                let mut local_count = 0;
                for TypedPattern { pattern, typ } in params {
                    local_count += self.push_names_in_pattern(&pattern);
                    resolved_params.push(TypedPattern {
                        typ: self.resolve_names_in_type_expr(typ)?,
                        pattern,
                    })
                }
                let body = self.resolve_names_in_expr(body)?;
                self.locals.truncate(self.locals.len() - local_count);

                let ret = if let Some(ret) = ret {
                    Some(self.resolve_names_in_type_expr(ret)?)
                } else {
                    None
                };

                Declaration::Function { name, params: resolved_params, body, ret }
            }
            // Imports are handled seperately. (see NameResolver::handle_imports)
            Declaration::Import { .. } => unreachable!(),
        };

        Ok(resolved_decl)
    }

    fn handle_imports(&mut self, imports: HashMap<Symbol, Import>) -> ResolutionResult<()> {
        for (name, Import { span, import_path, module }) in imports {
            let resolved_import = NameResolver::new()
                .resolve_names_in_module(module)
                .map_err(|error| {
                    ResolutionError::ImportError {
                        import_path: import_path.clone(),
                        error: Box::new(error),
                    }
                    .attach(span)
                })?;

            self.imports.insert(name, Import::new(span, import_path, resolved_import));
        }

        Ok(())
    }

    fn collect_declarations(&mut self, decls: &HashMap<Symbol, Declaration>) {
        // NOTE: Duplicate declarations are handled at the end of the parsing.
        for decl in decls.values() {
            #[allow(clippy::single_match)]
            match &decl {
                Declaration::Function { name, .. } => {
                    self.decls.insert(name.data.clone());
                }
                _ => (),
            }
        }
    }

    pub fn resolve_names_in_module(mut self, module: Module) -> ResolutionResult<Module> {
        self.collect_declarations(&module.decls);
        self.handle_imports(module.imports)?;

        let mut resolved_decls = HashMap::new();
        for (name, decl) in module.decls {
            resolved_decls.insert(name, self.resolve_names_in_decl(decl)?);
        }

        Ok(Module::new(resolved_decls, self.imports))
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

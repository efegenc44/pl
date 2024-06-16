use std::collections::HashSet;

use crate::frontend::span::{HasSpan, Spanned};

use super::ast::{Bound, Declaration, Expression, Pattern};

pub struct NameResolver<'source> {
    locals: Vec<&'source str>,
    globals: HashSet<&'source str>,
}

impl<'source> NameResolver<'source> {
    pub fn new() -> Self {
        Self { locals: Vec::new(), globals: HashSet::new() }
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
                    let name = self.globals.get(identifier)
                        .ok_or(Spanned::new(UnboundIndentifier(identifier), expr.span))?;

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
        };

        Ok(resolved_expr.attach(expr.span))
    }

    fn resolve_names_in_declaration(
        &mut self,
        decl: Spanned<'source, Declaration<'source>>
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
            },
            Declaration::Import { parts: _ } => todo!(),
        };

        Ok(resolved_decl.attach(decl.span))
    }

    fn collect_declarations(&mut self, decls: &Vec<Spanned<'source, Declaration<'source>>>) {
        for decl in decls {
            match &decl.data {
                Declaration::Function { name, .. } => {
                    // TODO: Handle duplicate function declarations
                    self.globals.insert(name.data);
                },
                _ => ()
            }
        }
    }

    pub fn resolve_names_in_program(
        &mut self,
        decls: Vec<Spanned<'source, Declaration<'source>>>,
    ) -> Result<Vec<Spanned<'source, Declaration<'source>>>, Spanned<'source, UnboundIndentifier<'source>>> {
        self.collect_declarations(&decls);

        let resolved_program = decls
            .into_iter()
            .map(|decl| self.resolve_names_in_declaration(decl))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(resolved_program)
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

pub struct UnboundIndentifier<'source>(pub &'source str);
type ResolutionResult<'a, T> =
    Result<Spanned<'a, T>, Spanned<'a, UnboundIndentifier<'a>>>;

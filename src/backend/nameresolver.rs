use crate::frontend::span::{HasSpan, Spanned};

use super::ast::{Bound, Expression, Pattern};

pub struct NameResolver<'source> {
    locals: Vec<&'source str>,
}

impl<'source> NameResolver<'source> {
    pub fn new() -> Self {
        Self { locals: Vec::new() }
    }

    pub fn resolve_names(
        &mut self,
        expr: Spanned<'source, Expression<'source>>,
    ) -> ResolutionResult<'source> {
        let resolved_expr = match expr.data {
            Expression::Integer(_) | Expression::Float(_) | Expression::String(_) => expr.data,
            Expression::Identifier(identifier, _) => {
                let indice = self
                    .locals
                    .iter()
                    .rev()
                    .position(|local| local == &identifier)
                    .ok_or(Spanned::new(UnboundIndentifier(identifier), expr.span))?;
                Expression::Identifier(identifier, Bound::Local(indice))
            }
            Expression::Binary { lhs, op, rhs } => Expression::Binary {
                lhs: Box::new(self.resolve_names(*lhs)?),
                op,
                rhs: Box::new(self.resolve_names(*rhs)?),
            },
            Expression::Application { expr, args } => Expression::Application {
                expr: Box::new(self.resolve_names(*expr)?),
                args: args
                    .into_iter()
                    .map(|arg| self.resolve_names(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Expression::Let {
                pattern,
                expr,
                body,
            } => {
                let expr = self.resolve_names(*expr)?;
                let local_count = self.push_names_in_pattern(&pattern);
                let body = self.resolve_names(*body)?;
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
                let body = self.resolve_names(*body)?;
                self.locals.truncate(self.locals.len() - local_count);

                Expression::Lambda {
                    params,
                    body: Box::new(body),
                }
            }
        };

        Ok(resolved_expr.attach(expr.span))
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
type ResolutionResult<'a> =
    Result<Spanned<'a, Expression<'a>>, Spanned<'a, UnboundIndentifier<'a>>>;

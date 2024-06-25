use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::{ast::{Bound, Declaration, Expression, Import, Module, Pattern, TypeExpr}, typ::Type};

pub struct  TypeChecker {
    locals: Vec<Type>,
    decls: HashMap<Symbol, Type>,
    imports: HashMap<Symbol, HashMap<Symbol, Type>>,
    types: HashMap<Symbol, Type>,
}

impl TypeChecker {
    pub fn new() -> Self {
        let primitive_types = HashMap::from([
            ("Integer".into(), Type::Integer),
            ("String".into(), Type::String),
            ("Float".into(), Type::Float),
            ("Nothing".into(), Type::Nothing),
        ]);

        Self {
            locals: Vec::new(),
            decls: HashMap::new(),
            imports: HashMap::new(),
            types: primitive_types,
        }
    }

    fn type_check_expr(&mut self, expr: &Expression) -> TypeCheckResult<Type> {
        let typ = match expr {
            Expression::Identifier(_, bound) => {
                match bound {
                    Bound::Local(indice) => self.locals[self.locals.len() - 1 - indice].clone(),
                    Bound::Global(identifier) => self.decls[identifier].clone(),
                    Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
                }
            },
            Expression::Integer(_) => Type::Integer,
            Expression::Float(_) => Type::Float,
            Expression::String(_) => Type::String,
            Expression::Nothing(_) => Type::Nothing,
            Expression::Binary { lhs, op: _, rhs } => {
                self.type_check_expr(lhs)?;
                self.type_check_expr(rhs)?;
                todo!("Type Checking of Binary Exprssions");
            },
            Expression::Application { expr, args } => {
                let typ = self.type_check_expr(expr)?;
                let Type::Function { params, ret } = typ else {
                    return Err(TypeCheckError::ExpectedFunction(typ).attach(expr.span()))
                };

                if args.len() != params.len() {
                    return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: args.len() }.attach(expr.span()))
                }

                for (arg, param) in iter::zip(args, params) {
                    self.expect_type(arg, &param)?;
                }

                *ret
            },
            Expression::Let { pattern, typ, expr, body } => {
                let typ = if let Some(typ) = typ {
                    let typ = self.eval_type_expr(typ);
                    self.expect_type(expr, &typ)?;
                    typ
                } else {
                    self.type_check_expr(expr)?
                };

                let local_count = self.push_types_in_pattern(pattern, typ)?;
                let result = self.type_check_expr(body)?;
                self.locals.truncate(self.locals.len() - local_count);

                result
            },
            Expression::Lambda { params: _, body: _ } => {
                todo!("Type Checking of Lambdas")
            },
            Expression::Access { module_name, name } => {
                self.imports[&module_name.data][&name.data].clone()
            },
        };

        Ok(typ)
    }

    fn push_types_in_pattern(&mut self, pattern: &Pattern, typ: Type) -> TypeCheckResult<usize> {
        match (pattern, &typ) {
            (Pattern::Any(_), _) => {
                self.locals.push(typ);
                Ok(1)
            },
            (Pattern::String(_), Type::String)
            | (Pattern::Integer(_), Type::Integer)
            | (Pattern::Float(_), Type::Float) => Ok(0),
            _ => Err(TypeCheckError::PatternMismatch(typ).attach(pattern.span()))
        }
    }

    fn expect_type(&mut self, expr: &Expression, expected: &Type) -> TypeCheckResult<()> {
        let found = self.type_check_expr(expr)?;
        if &self.type_check_expr(expr)? != expected {
            return Err(TypeCheckError::TypeMismatch { expected: expected.clone(), found }.attach(expr.span()))
        }

        Ok(())
    }

    fn eval_type_expr(&mut self, type_expr: &TypeExpr) -> Type {
        match type_expr {
            TypeExpr::Identifier(_, bound) => {
                match bound {
                    Bound::Local(_indice) => todo!("Local Type Variables"),
                    Bound::Global(identifier) => self.types[identifier].clone(),
                    Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
                }
            },
            TypeExpr::Function { params, ret } => {
                let params = params.iter().map(|param| self.eval_type_expr(param)).collect();
                let ret = Box::new(self.eval_type_expr(ret));

                Type::Function { params, ret }
            },
        }
    }

    fn type_check_decl(&mut self, decl: &Declaration) -> TypeCheckResult<()> {
        match decl {
            Declaration::Function { name, params: _, body, ret: _ } => {
                let Type::Function { params, ret } = self.decls[&name.data].clone() else {
                    unreachable!()
                };

                for param in params {
                    self.locals.push(param);
                }
                self.expect_type(body, &ret)?;
                Ok(())
            },
            // Imports are handled seperately. (see TypeChecker::handle_imports)
            Declaration::Import { .. } => unreachable!(),
        }
    }

    pub fn type_check_module(&mut self, module: &Module) -> TypeCheckResult<()> {
        self.collect_declarations(&module.decls);
        self.handle_imports(&module.imports)?;

        for decl in module.decls.values() {
            self.type_check_decl(decl)?;
        }

        Ok(())
    }

    fn handle_imports(&mut self, imports: &HashMap<Symbol, Import>) -> TypeCheckResult<()>{
        for (name, Import { span, import_path, module }) in imports {
            let mut type_checker = TypeChecker::new();
            type_checker
                .type_check_module(module)
                .map_err(|error| {
                    TypeCheckError::ImportError {
                        import_path: import_path.clone(),
                        error: Box::new(error),
                    }
                    .attach(*span)
                })?;

            self.imports.insert(name.clone(), type_checker.decls);
        }

        Ok(())
    }

    fn collect_declarations(&mut self, decls: &HashMap<Symbol, Declaration>) {
        for decl in decls.values() {
            #[allow(clippy::single_match)]
            match &decl {
                Declaration::Function { name, params, body: _, ret  } => {
                    let typ = Type::Function {
                        params: params
                            .iter()
                            .map(|param| self.eval_type_expr(&param.typ))
                            .collect(),
                        ret: Box::new(ret.as_ref().map_or(Type::Nothing, |ret| self.eval_type_expr(ret))),
                    };

                    self.decls.insert(name.data.clone(), typ);
                }
                _ => (),
            }
        }
    }
}

pub enum TypeCheckError {
    TypeMismatch {
        expected: Type,
        found: Type,
    },
    PatternMismatch(Type),
    ImportError {
        import_path: Symbol,
        error: Box<Spanned<TypeCheckError>>,
    },
    ExpectedFunction(Type),
    ArityMismatch {
        expected: usize,
        found: usize,
    }
}

impl Display for TypeCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeMismatch { expected, found } => write!(f, "Expected `{expected}` but found `{found}`."),
            Self::PatternMismatch(typ) => write!(f, "Pattern is not suitable for `{typ}`."),
            Self::ImportError { .. } => write!(f, "Error while importing module."),
            Self::ExpectedFunction(typ) => write!(f, "Expected a function type but found `{typ}`."),
            Self::ArityMismatch { expected, found } => write!(f, "Expected `{expected}` arguments but found `{found}`."),
        }
    }
}

impl HasSpan for TypeCheckError {}

type TypeCheckResult<T> = Result<T, Spanned<TypeCheckError>>;



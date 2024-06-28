use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::{ast::{Bound, Expression, Namespace, Pattern, TypeExpr}, module::{self, Function, Import, Module}, typ::{self, Type}};

pub struct  TypeChecker {
    interface: Interface,
    locals: Vec<Type>,
}

impl TypeChecker {
    pub fn new() -> Self {
        // let primitive_types: HashMap<Symbol, Type> = HashMap::from([
        //     ("Integer".into(), (Type::Integer)),
        //     ("String".into(), Type::String),
        //     ("Float".into(), Type::Float),
        //     ("Nothing".into(), Type::Nothing),
        // ]);

        Self {
            interface: Interface::default(),
            locals: Vec::new(),
        }
    }

    pub fn type_check_expr(&mut self, expr: &Expression) -> TypeCheckResult<Type> {
        let typ = match expr {
            Expression::Identifier(_, bound) => {
                match bound {
                    Bound::Local(indice) => self.locals[self.locals.len() - 1 - indice].clone(),
                    Bound::Global(identifier) => {
                        let (params, ret) = self.interface.function_types[identifier].clone();
                        Type::Function { params, ret: Box::new(ret) }
                    },
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
            Expression::Access { from, name, namespace } => {
                match namespace {
                    Namespace::Type => {
                        let ret = self.interface.types[&from.data].clone();
                        let params = self.interface.constructors[&from.data][&name.data].clone();
                        Type::Function { params, ret: Box::new(ret) }
                    }
                    Namespace::Import => {
                        let (params, ret) = self.interface.imports[&from.data].function_types[&name.data].clone();
                        Type::Function { params, ret: Box::new(ret) }
                    },
                    Namespace::Undetermined => unreachable!(),
                }

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
                    Bound::Global(identifier) => self.interface.types[identifier].clone(),
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

    fn type_check_function(&mut self, function: &Function) -> TypeCheckResult<()> {
        let Function { name, params: patterns, body, ret: _ } = function;
        let (params, ret) = self.interface.function_types[&name.data].clone();

        for (pattern, typ) in iter::zip(patterns, params) {
            self.push_types_in_pattern(&pattern.pattern, typ)?;
        }

        self.expect_type(body, &ret)?;
        Ok(())
    }

    fn type_check_type(&mut self, typ: &module::Type) -> TypeCheckResult<()> {
        let mut map = HashMap::new();
        for (name, params) in &typ.consts {
            let params = params
                .iter()
                .map(|param| self.eval_type_expr(param))
                .collect();
            map.insert(name.data.clone(), params);
        }
        self.interface.constructors.insert(typ.name.data.clone(), map);

        Ok(())
    }

    fn import_interface(&mut self, imports: &HashMap<Symbol, Import>) -> TypeCheckResult<()> {
        for (name, Import { parts, module }) in imports {
            let mut type_checker = Self::new();
            type_checker.type_check_module(module).map_err(|error| {
                // TODO: Do not hardcode the file extension.
                let import_path = parts.iter().fold(String::from("."), |mut acc, part| {
                    acc.push('\\');
                    acc.push_str(&part.data);
                    acc
                }) + ".txt";

                let first = parts.first().unwrap().span;
                let last = parts.last().unwrap().span;
                let span = first.extend(last);
                TypeCheckError::ImportError {
                    import_path: import_path.into(),
                    error: Box::new(error),
                }
                .attach(span)
            })?;
            self.interface.imports.insert(name.clone(), type_checker.interface);
        }

        Ok(())
    }

    fn type_interface(&mut self, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts: _ } in types.values() {
            self.interface.types.insert(name.data.clone(), Type::Custom(name.data.clone()));
        }
    }

    fn function_interface(&mut self, functions: &HashMap<Symbol, Function>) {
        for Function { name, params, body: _, ret } in functions.values() {
            let function_type = (
                params
                    .iter()
                    .map(|param| self.eval_type_expr(&param.typ))
                    .collect(),
                ret.as_ref().map_or(Type::Nothing, |ret| self.eval_type_expr(ret))
            );

            self.interface.function_types.insert(name.data.clone(), function_type);
        }
    }


    pub fn type_check_module(&mut self, module: &Module) -> TypeCheckResult<()> {
        self.import_interface(&module.imports)?;
        self.type_interface(&module.types);
        self.function_interface(&module.functions);

        for typ in module.types.values() {
            self.type_check_type(typ)?;
        }

        for function in module.functions.values() {
            self.type_check_function(function)?;
        }

        Ok(())
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

#[derive(Default)]
pub struct Interface {
    function_types: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
    imports: HashMap<Symbol, Interface>,
    types: HashMap<Symbol, typ::Type>,
    constructors: HashMap<Symbol, HashMap<Symbol, Vec<typ::Type>>>
}


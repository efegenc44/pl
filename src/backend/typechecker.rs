use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::{ast::{Bound, Expression, Namespace, Pattern, TypeExpr}, module::{self, Function, Import, Module}, typ::{self, Type}};

pub struct  TypeChecker {
    interface: Interface,
    locals: Vec<Type>,
}

impl TypeChecker {
    pub fn new(module: &Module) -> Self {
        let mut type_checker = Self {
            interface: Default::default(),
            locals: Vec::new(),
        };

        // NOTE: Order here is important! (imports => types => constructors => functions)
        type_checker.import_interface(&module.imports);
        type_checker.type_interface(&module.types);
        type_checker.constructor_interface(&module.types);
        type_checker.function_interface(&module.functions);

        type_checker
    }

    pub fn type_check_module(module: &Module) -> TypeCheckResult<Interface> {
        let mut type_checker = Self::new(module);

        for import in module.imports.values() {
            Self::type_check_import(import)?;
        }

        for function in module.functions.values() {
            type_checker.type_check_function(function)?;
        }

        Ok(type_checker.interface)
    }

    pub fn type_check_expr(&mut self, expr: &Expression) -> TypeCheckResult<Type> {
        let typ = match expr {
            Expression::Identifier(_, bound) => {
                match bound {
                    Bound::Local(indice) => self.locals[self.locals.len() - 1 - indice].clone(),
                    Bound::Global(identifier) => {
                        let (params, ret) = self.interface.functions[identifier].clone();
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
            Expression::Let { pattern, type_expr, expr, body } => {
                let typ = if let Some(typ) = type_expr {
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
            Expression::Access { path, namespace } => {
                match &path[..] {
                    [_] | [] => unreachable!(),
                    [from, name] => {
                        match namespace {
                            Namespace::Type => {
                                // TODO: If constructor does not take any arguments, does not return a function type
                                let ret = self.interface.types[&from.data].clone();
                                let params = self.interface.constructors[&from.data][&name.data].clone();
                                Type::Function { params, ret: Box::new(ret) }
                            }
                            Namespace::Module => {
                                let ImportTypes::Module { functions, .. } = &self.interface.imports[&from.data] else {
                                    unreachable!()
                                };

                                let (params, ret) = functions[&name.data].clone();
                                Type::Function { params, ret: Box::new(ret) }
                            },
                            Namespace::Undetermined => unreachable!(),
                        }

                    }
                    [modules@.., before, last] => {
                        let from = &modules.first().unwrap();
                        let mut current_import = &self.interface.imports[&from.data];

                        for module in &modules[1..] {
                            let ImportTypes::Group(modules) = current_import else {
                                unreachable!()
                            };

                            current_import = &modules[&module.data];
                        }

                        match namespace {
                            Namespace::Type => {
                                let ImportTypes::Module { types, constructors, .. } = current_import else {
                                    unreachable!()
                                };

                                let ret = types[&before.data].clone();
                                let params = constructors[&before.data][&last.data].clone();
                                Type::Function { params, ret: Box::new(ret) }
                            }
                            Namespace::Module => {
                                let ImportTypes::Group(modules) = current_import else {
                                    unreachable!()
                                };

                                let ImportTypes::Module { functions, .. } = &modules[&before.data] else {
                                    unreachable!()
                                };

                                let (params, ret) = functions[&last.data].clone();
                                Type::Function { params, ret: Box::new(ret) }
                            },
                            Namespace::Undetermined => unreachable!(),
                        }
                    }
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
            TypeExpr::Access { path } => {
                match &path[..] {
                    [_] | [] => unreachable!(),
                    [from, name] => {
                        let ImportTypes::Module { types, .. } = &self.interface.imports[&from.data] else {
                            unreachable!()
                        };

                        types[&name.data].clone()
                    }
                    [modules@.., before, last] => {
                        let from = &modules.first().unwrap();
                        let mut current_import = &self.interface.imports[&from.data];

                        for module in &modules[1..] {
                            let ImportTypes::Group(modules) = current_import else {
                                unreachable!()
                            };

                            current_import = &modules[&module.data];
                        }

                        let ImportTypes::Group(modules) = current_import else {
                            unreachable!()
                        };

                        let ImportTypes::Module { types, .. } = &modules[&before.data] else {
                            unreachable!()
                        };

                        types[&last.data].clone()
                    }
                }
            }
        }
    }

    fn type_check_function(&mut self, function: &Function) -> TypeCheckResult<()> {
        let Function { name, params: patterns, body, ret: _ } = function;
        let (params, ret) = self.interface.functions[&name.data].clone();

        for (pattern, typ) in iter::zip(patterns, params) {
            self.push_types_in_pattern(&pattern.pattern, typ)?;
        }

        self.expect_type(body, &ret)
    }

    fn type_check_import(Import { parts, kind }: &Import) -> TypeCheckResult<()> {
        match kind {
            module::ImportKind::File(module) => {
                Self::type_check_module(module).map_err(|error| {
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
            },
            module::ImportKind::Folder(imports) => {
                for (_, import) in imports {
                    Self::type_check_import(import)?;
                }
            },
        }

        Ok(())
    }

    fn type_interface(&mut self, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts: _ } in types.values() {
            self.interface.types.insert(name.data.clone(), Type::Custom(name.data.clone()));
        }
    }

    fn constructor_interface(&mut self, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts } in types.values() {
            let mut map = HashMap::new();
            for (name, params) in consts {
                let params = params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect();
                map.insert(name.data.clone(), params);
            }
            self.interface.constructors.insert(name.data.clone(), map);
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

            self.interface.functions.insert(name.data.clone(), function_type);
        }
    }

    fn get_import_types(Import { parts: _, kind }: &Import) -> ImportTypes {
            match kind {
                module::ImportKind::File(module) => {
                    let resolver = Self::new(&module);
                    ImportTypes::Module {
                        functions: resolver.interface.functions,
                        types: resolver.interface.types,
                        constructors: resolver.interface.constructors,
                    }
                },
                module::ImportKind::Folder(imports) => {
                    let modules = imports.iter().map(|(name, import)| (name.clone(), Self::get_import_types(import))).collect();
                    ImportTypes::Group(modules)
                },
            }
    }

    fn import_interface(&mut self, imports: &HashMap<Box<str>, Import>) {
        for (name, import) in imports {
            self.interface.imports.insert(name.clone(), Self::get_import_types(import));
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

#[derive(Default)]
pub struct Interface {
    functions: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
    imports: HashMap<Symbol, ImportTypes>,
    types: HashMap<Symbol, typ::Type>,
    constructors: HashMap<Symbol, HashMap<Symbol, Vec<typ::Type>>>,
}

enum ImportTypes {
    Module {
        functions: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
        types: HashMap<Symbol, typ::Type>,
        constructors: HashMap<Symbol, HashMap<Symbol, Vec<typ::Type>>>,
    },
    Group(HashMap<Symbol, ImportTypes>)
}

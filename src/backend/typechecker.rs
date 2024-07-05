use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::{ast::{Access, Application, Binary, Bound, Expression, TypeFunction, Lambda, Let, Namespace, Pattern, TypeExpression}, module::{self, Function, Import, Module}, typ::{self, Type}};

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
        match expr {
            Expression::Identifier(_, bound) => self.type_check_identifier(bound),
            Expression::Integer(_) => Ok(Type::Integer),
            Expression::Float(_) => Ok(Type::Float),
            Expression::String(_) => Ok(Type::String),
            Expression::Nothing(_) => Ok(Type::Nothing),
            Expression::Binary(Binary { lhs, op: _, rhs }) => {
                self.type_check_expr(lhs)?;
                self.type_check_expr(rhs)?;
                todo!("Type Checking of Binary Exprssions");
            },
            Expression::Application(application) => self.type_check_application(application),
            Expression::Let(lett) => self.type_check_let(lett),
            Expression::Lambda(Lambda { params: _, body: _ }) => {
                todo!("Type Checking of Lambdas")
            },
            Expression::Access(access) => self.type_check_access(access),
        }
    }

    fn type_check_identifier(&self, bound: &Bound) -> TypeCheckResult<Type> {
        match bound {
            Bound::Local(indice) => Ok(self.locals[self.locals.len() - 1 - indice].clone()),
            Bound::Global(identifier) => {
                let (params, ret) = self.interface.functions[identifier].clone();
                Ok(Type::Function { params, ret: Box::new(ret) })
            },
            // TODO: Remove to_vec
            Bound::Absolute(path) => self.type_check_access(&Access { path: path.to_vec(), namespace: Namespace::Module }),
            Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
        }
    }

    fn type_check_application(&mut self, Application { expr, args }: &Application) -> TypeCheckResult<Type> {
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

        Ok(*ret)
    }

    fn type_check_let(&mut self, Let { expr, type_expr, branches }: &Let) -> TypeCheckResult<Type> {
        // Exhaustiveness check.

        let typ = if let Some(typ) = type_expr {
            let typ = self.eval_type_expr(typ);
            self.expect_type(expr, &typ)?;
            typ
        } else {
            self.type_check_expr(expr)?
        };

        let first_branch = branches.first().unwrap();

        let local_count = self.push_types_in_pattern(&first_branch.0, &typ)?;
        let result = self.type_check_expr(&first_branch.1)?;
        self.locals.truncate(self.locals.len() - local_count);

        for (pattern, body) in &branches[1..] {
            let local_count = self.push_types_in_pattern(pattern, &typ)?;
            self.expect_type(body, &result)?;
            self.locals.truncate(self.locals.len() - local_count);
            assert!(self.locals.is_empty())
        }

        Ok(result)
    }

    fn type_check_access(&self, Access { path, namespace }: &Access) -> TypeCheckResult<Type> {
        match &path[..] {
            [_] | [] => unreachable!(),
            [from, name] => {
                match namespace {
                    Namespace::Type => {
                        // TODO: If constructor does not take any arguments, does not return a function type
                        let ret = self.interface.types[&from.data].clone();
                        let params = self.interface.constructors[&from.data][&name.data].clone();
                        Ok(Type::Function { params, ret: Box::new(ret) })
                    }
                    Namespace::Module => {
                        let ImportTypes::Module { functions, .. } = &self.interface.imports[&from.data] else {
                            unreachable!()
                        };

                        let (params, ret) = functions[&name.data].clone();
                        Ok(Type::Function { params, ret: Box::new(ret) })
                    },
                    Namespace::Undetermined => unreachable!(),
                }
            }
            [groups@.., from, name] => {
                let first = &groups.first().unwrap();
                let mut current_import = &self.interface.imports[&first.data];

                for module in &groups[1..] {
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

                        let ret = types[&from.data].clone();
                        let params = constructors[&from.data][&name.data].clone();
                        Ok(Type::Function { params, ret: Box::new(ret) })
                    }
                    Namespace::Module => {
                        let ImportTypes::Group(modules) = current_import else {
                            unreachable!()
                        };

                        let ImportTypes::Module { functions, .. } = &modules[&from.data] else {
                            unreachable!()
                        };

                        let (params, ret) = functions[&name.data].clone();
                        Ok(Type::Function { params, ret: Box::new(ret) })
                    },
                    Namespace::Undetermined => unreachable!(),
                }
            }
        }
    }

    fn push_types_in_pattern(&mut self, pattern: &Pattern, typ: &Type) -> TypeCheckResult<usize> {
        match (pattern, &typ) {
            (Pattern::Any(_), _) => {
                self.locals.push(typ.clone());
                Ok(1)
            },
            (Pattern::String(_), Type::String)
            | (Pattern::Integer(_), Type::Integer)
            | (Pattern::Float(_), Type::Float) => Ok(0),
            (Pattern::Constructor { path, params }, Type::Custom(type_name)) => {
                let Type::Function { params: cparams, ret: _ } = (match &path[..] {
                    [_] => todo!(),
                    [path@.., name] => {
                        let Type::Custom(typ_name) = self.type_check_type_access(path) else {
                            unreachable!();
                        };

                        if &typ_name != type_name {
                            return Err(TypeCheckError::PatternMismatch(typ.clone()).attach(pattern.span()))
                        }

                        let mut path = path.to_vec();
                        path.push(name.clone());
                        self.type_check_access(&(Access {
                            path,
                            namespace: Namespace::Type,
                        }))?
                    },
                    _ => unreachable!(),
                }) else {
                    unreachable!()
                };

                if cparams.len() != params.len() {
                    return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: cparams.len() }.attach(pattern.span()))
                }

                let mut local_count = 0;
                for (cparam, param) in iter::zip(cparams, params) {
                    local_count += self.push_types_in_pattern(param, &cparam)?;
                }

                Ok(local_count)
            },
            _ => Err(TypeCheckError::PatternMismatch(typ.clone()).attach(pattern.span()))
        }
    }

    fn expect_type(&mut self, expr: &Expression, expected: &Type) -> TypeCheckResult<()> {
        let found = self.type_check_expr(expr)?;
        if &self.type_check_expr(expr)? != expected {
            return Err(TypeCheckError::TypeMismatch { expected: expected.clone(), found }.attach(expr.span()))
        }

        Ok(())
    }

    fn eval_type_expr(&mut self, type_expr: &TypeExpression) -> Type {
        match type_expr {
            TypeExpression::Identifier(_, bound) => {
                match bound {
                    Bound::Local(_indice) => todo!("Local Type Variables"),
                    Bound::Global(identifier) => self.interface.types[identifier].clone(),
                    Bound::Absolute(path) => self.type_check_type_access(&path),
                    Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
                }
            },
            TypeExpression::Function(TypeFunction { params, ret }) => {
                let params = params.iter().map(|param| self.eval_type_expr(param)).collect();
                let ret = Box::new(self.eval_type_expr(ret));

                Type::Function { params, ret }
            },
            TypeExpression::Access(path) => self.type_check_type_access(path),
        }
    }

    fn type_check_type_access(&self, path: &[Spanned<Symbol>]) -> Type {
        match &path[..] {
            [] => unreachable!(),
            [from] => {
                self.interface.types[&from.data].clone()
            }
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

    fn type_check_function(&mut self, Function { name, params:_ , ret: _, branches }: &Function) -> TypeCheckResult<()> {
        let (params, ret) = self.interface.functions[&name.data].clone();

        for (patterns, body) in branches {
            let mut local_count = 0;
            for (pattern, typ) in iter::zip(patterns, &params) {
                local_count += self.push_types_in_pattern(pattern, &typ)?;
            }
            self.expect_type(body, &ret)?;
            self.locals.truncate(self.locals.len() - local_count);
            assert!(self.locals.is_empty())
        }

        Ok(())
    }

    fn type_check_import(Import { parts, kind, directs: _ }: &Import) -> TypeCheckResult<()> {
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
        for Function { name, params, ret, branches: _ } in functions.values() {
            let function_type = (
                params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect(),
                ret.as_ref().map_or(Type::Nothing, |ret| self.eval_type_expr(ret))
            );

            self.interface.functions.insert(name.data.clone(), function_type);
        }
    }

    fn get_import_types(Import { parts: _, kind, directs: _ }: &Import) -> ImportTypes {
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
    },
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

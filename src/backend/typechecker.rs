use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::{ast::{AbsoluteBound, Application, Bound, Expression, Let, Pattern, TypeExpression, TypeFunction}, module::{self, Function, Import, Module}, typ::{self, Type}};

pub struct  TypeChecker {
    modules: HashMap<Symbol, Types>,
    locals: Vec<Type>,
}

impl TypeChecker {
    pub fn new(module: &Module) -> Self {
        let mut type_checker = Self {
            locals: Vec::new(),
            modules: HashMap::new(),
        };

        type_checker.modules.insert(module.path.clone(), Types::default());

        // NOTE: Order here is important! (imports => types => constructors => functions)
        type_checker.import_interface(&module.imports);
        type_checker.type_interface(&module.path, &module.types);
        type_checker.constructor_interface(&module.path, &module.types);
        type_checker.function_interface(&module.path, &module.functions);

        type_checker
    }

    pub fn type_check_module(&mut self, module: &Module) -> TypeCheckResult<()> {
        for import in module.imports.values() {
            self.type_check_import(import)?;
        }

        for function in module.functions.values() {
            self.type_check_function(&module.path, function)?;
        }

        Ok(())
    }

    pub fn type_check_expr(&mut self, expr: &Expression) -> TypeCheckResult<Type> {
        match expr {
            Expression::Identifier(_, bound) => self.type_check_identifier(bound),
            Expression::Integer(_) => Ok(Type::Integer),
            Expression::Float(_) => Ok(Type::Float),
            Expression::String(_) => Ok(Type::String),
            Expression::Nothing(_) => Ok(Type::Nothing),
            Expression::Application(application) => self.type_check_application(application),
            Expression::Let(lett) => self.type_check_let(lett),
            Expression::Access(access) => Ok(self.type_check_access(&access.abs_bound)),
        }
    }

    fn type_check_identifier(&self, bound: &Bound) -> TypeCheckResult<Type> {
        match bound {
            Bound::Local(indice) => Ok(self.locals[self.locals.len() - 1 - indice].clone()),
            // TODO: Remove to_vec
            Bound::Absolute(abs_bound) => Ok(self.type_check_access(abs_bound)),
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

    fn type_check_access(&self, abs_bound: &AbsoluteBound) -> Type {
        match abs_bound {
            AbsoluteBound::FromModule { module, name } => {
                let (params, ret) = (&self.modules[module].functions)[name].clone();
                Type::Function { params, ret: Box::new(ret) }
            },
            AbsoluteBound::Constructor { module, typ, name } => {
                let interface = &self.modules[module];
                // TODO: If constructor does not take any arguments, does not return a function type
                let ret = interface.types[typ].clone();
                let params = interface.constructors[typ][name].clone();
                Type::Function { params, ret: Box::new(ret) }
            }
            AbsoluteBound::Undetermined => unreachable!("Name Resolver must've resolved all access expressions."),
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
            (Pattern::Constructor { path: _, params, abs_bound }, Type::Custom(type_name)) => {
                let Type::Function { params: cparams, ret: _ } = (match abs_bound {
                    AbsoluteBound::Constructor { module, typ: typ_name, name: _ } => {
                        let Type::Custom(typ_name) = self.type_check_type_access(module, typ_name) else {
                            unreachable!();
                        };

                        if &typ_name != type_name {
                            return Err(TypeCheckError::PatternMismatch(typ.clone()).attach(pattern.span()))
                        }

                        self.type_check_access(abs_bound)
                    },
                    AbsoluteBound::FromModule { .. } => unreachable!(),
                    AbsoluteBound::Undetermined => unreachable!(),
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
                    Bound::Absolute(abs_bound) => {
                        let AbsoluteBound::FromModule { module, name } = abs_bound else {
                            unreachable!()
                        };

                        self.type_check_type_access(module, name)
                    },
                    Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
                }
            },
            TypeExpression::Function(TypeFunction { params, ret }) => {
                let params = params.iter().map(|param| self.eval_type_expr(param)).collect();
                let ret = Box::new(self.eval_type_expr(ret));

                Type::Function { params, ret }
            },
            TypeExpression::Access(_, abs_bound) => {
                let AbsoluteBound::FromModule { module, name } = abs_bound else {
                    unreachable!()
                };

                self.type_check_type_access(module, name)
            },
        }
    }

    fn type_check_type_access(&self, module: &Symbol, typ: &Symbol) -> Type {
        let types = &self.modules[module];
        // dbg!(types.types.keys());
        // dbg!(module);
        // dbg!(typ);
        types.types[typ].clone()
    }

    fn type_check_function(&mut self, module_path: &Symbol, Function { name, params:_ , ret: _, branches }: &Function) -> TypeCheckResult<()> {
        let (params, ret) = self.modules[module_path].functions[&name.data].clone();

        for (patterns, body) in branches {
            if patterns.len() != params.len() {
                return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: patterns.len() }.attach(name.span))
            }

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

    fn type_check_import(&mut self, Import { parts, kind, directs: _ }: &Import) -> TypeCheckResult<()> {
        match kind {
            module::ImportKind::File(module) => {
                self.type_check_module(module).map_err(|error| {
                    let first = parts.first().unwrap().span;
                    let last = parts.last().unwrap().span;
                    let span = first.extend(last);
                    TypeCheckError::ImportError {
                        import_path: module.path.clone().into(),
                        error: Box::new(error),
                    }
                    .attach(span)
                })?;
            },
            module::ImportKind::Folder((imports, _path)) => {
                for (_, import) in imports {
                    self.type_check_import(import)?;
                }
            },
        }

        Ok(())
    }

    fn type_interface(&mut self, module_path: &Symbol, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts: _ } in types.values() {
            self.modules.get_mut(module_path).unwrap().types.insert(name.data.clone(), Type::Custom(name.data.clone()));
        }
    }

    fn constructor_interface(&mut self, module_path: &Symbol, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts } in types.values() {
            let mut map = HashMap::new();
            for (name, params) in consts {
                let params = params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect();
                map.insert(name.data.clone(), params);
            }

            self.modules.get_mut(module_path).unwrap().constructors.insert(name.data.clone(), map);
        }
    }

    fn function_interface(&mut self, module_path: &Symbol, functions: &HashMap<Symbol, Function>) {
        for Function { name, params, ret, branches: _ } in functions.values() {
            let function_type = (
                params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect(),
                ret.as_ref().map_or(Type::Nothing, |ret| self.eval_type_expr(ret))
            );

            self.modules.get_mut(module_path).unwrap().functions.insert(name.data.clone(), function_type);
        }
    }

    fn get_import_types(&mut self, Import { parts: _, kind, directs: _ }: &Import) {
        match kind {
            module::ImportKind::File(module) => {
                if self.modules.contains_key(&module.path) {
                    // already encountered the module.
                    return;
                }

                self.modules.insert(module.path.clone(), Types::default());

                // NOTE: Order here is important! (imports => types => constructors => functions)
                self.import_interface(&module.imports);
                self.type_interface(&module.path, &module.types);
                self.constructor_interface(&module.path, &module.types);
                self.function_interface(&module.path, &module.functions);
            },
            module::ImportKind::Folder((imports, _path)) => {
                self.import_interface(imports);
            },
        }
    }

    fn import_interface(&mut self, imports: &HashMap<Box<str>, Import>) {
        for (_, import) in imports {
            self.get_import_types(import);
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

#[derive(Default, Debug)]
pub struct Types {
    functions: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
    types: HashMap<Symbol, typ::Type>,
    constructors: HashMap<Symbol, HashMap<Symbol, Vec<typ::Type>>>,
}

use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Spanned}, token::Symbol};

use super::{ast::{Access, Application, Bound, Expression, TypeFunction, Let, Namespace, Pattern, TypeExpression}, module::{self, Function, Import, Module}, typ::{self, Type}};

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
        type_checker.type_interface(None, &module.types);
        type_checker.constructor_interface(None, &module.types);
        type_checker.function_interface(None, &module.functions);

        type_checker
    }

    pub fn type_check_module(&mut self, module: &Module) -> TypeCheckResult<()> {
        for import in module.imports.values() {
            self.type_check_import(import)?;
        }

        for function in module.functions.values() {
            let module_path = if module.path.is_empty() {
                None
            } else {
                Some(module.path.clone())
            };

            self.type_check_function(module_path.map(|a| vec![a]), function)?;
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
            Expression::Access(access) => Ok(self.type_check_access(access)),
        }
    }

    fn type_check_identifier(&self, bound: &Bound) -> TypeCheckResult<Type> {
        match bound {
            Bound::Local(indice) => Ok(self.locals[self.locals.len() - 1 - indice].clone()),
            // TODO: Remove to_vec
            Bound::Absolute(path) => Ok(self.type_check_access(&Access { path: vec![], namespace: Namespace::Module, real_path: path.to_vec() })),
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

    fn type_check_access(&self, Access { path: _, namespace, real_path }: &Access) -> Type {
        match &real_path[..] {
            [] => unreachable!(),
            [name] => {
                let (params, ret) = self.interface.functions[name].clone();
                Type::Function { params, ret: Box::new(ret) }
            }
            [a@.., from, name] => {
                match namespace {
                    Namespace::Type => {
                        if a.is_empty() {
                            // TODO: If constructor does not take any arguments, does not return a function type
                            let ret = self.interface.types[from].clone();
                            let params = self.interface.constructors[from][name].clone();
                            Type::Function { params, ret: Box::new(ret) }
                        } else {
                            // let path: Vec<_> = path.iter().map(|part| part.data.clone()).collect();
                            // dbg!(path);
                            // dbg!(real_path);
                            // dbg!(a);
                            let interface = &self.interface.imports[a];
                            // TODO: If constructor does not take any arguments, does not return a function type
                            let ret = interface.types[from].clone();
                            let params = interface.constructors[from][name].clone();
                            Type::Function { params, ret: Box::new(ret) }
                        }
                    }
                    Namespace::Module => {
                        let mut a = a.to_vec();
                        a.push(from.clone());
                        let (params, ret) = (&self.interface.imports[&a].functions)[name].clone();
                        Type::Function { params, ret: Box::new(ret) }
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
            (Pattern::Constructor { path: _, params, real_path }, Type::Custom(type_name)) => {
                let Type::Function { params: cparams, ret: _ } = (match &real_path[..] {
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
                            path: vec![],
                            namespace: Namespace::Type,
                            real_path: real_path.clone(),
                        }))
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
                    Bound::Absolute(path) => self.type_check_type_access(path),
                    Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
                }
            },
            TypeExpression::Function(TypeFunction { params, ret }) => {
                let params = params.iter().map(|param| self.eval_type_expr(param)).collect();
                let ret = Box::new(self.eval_type_expr(ret));

                Type::Function { params, ret }
            },
            TypeExpression::Access(_, real_path) => {
                let real_path: Vec<_> = real_path.iter().map(|part| part.clone()).collect();
                self.type_check_type_access(&real_path)
            },
        }
    }

    fn type_check_type_access(&self, path: &[Symbol]) -> Type {
        match &path[..] {
            [] => unreachable!(),
            [from] => {
                self.interface.types[from].clone()
            }
            [from@.., name] => {
                // dbg!(self.interface.imports.keys());
                // dbg!(from);
                // dbg!(name);
                (&self.interface.imports[from].types)[name].clone()
            }
        }
    }

    fn type_check_function(&mut self, module_path: Option<Vec<Symbol>>, Function { name, params:_ , ret: _, branches }: &Function) -> TypeCheckResult<()> {
        let (params, ret) = if let Some(module_path) = module_path.clone() {
            let a = &self.interface.imports[&module_path];
            a.functions[&name.data].clone()
        } else {
            self.interface.functions[&name.data].clone()
        };

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

    fn type_check_import(&mut self, Import { parts, kind, directs: _ }: &Import) -> TypeCheckResult<()> {
        match kind {
            module::ImportKind::File((module, _path)) => {
                self.type_check_module(module).map_err(|error| {
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
            module::ImportKind::Folder((imports, _path)) => {
                for (_, import) in imports {
                    self.type_check_import(import)?;
                }
            },
        }

        Ok(())
    }

    fn type_interface(&mut self, module_path: Option<Vec<Symbol>>, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts: _ } in types.values() {
            if let Some(module_path) = module_path.clone() {
                self.interface.imports.get_mut(&module_path).unwrap().types.insert(name.data.clone(), Type::Custom(name.data.clone()));
            } else{
                self.interface.types.insert(name.data.clone(), Type::Custom(name.data.clone()));
            }
        }
    }

    fn constructor_interface(&mut self, module_path: Option<Vec<Symbol>>, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts } in types.values() {
            let mut map = HashMap::new();
            for (name, params) in consts {
                let params = params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect();
                map.insert(name.data.clone(), params);
            }

            if let Some(module_path) = module_path.clone() {
                self.interface.imports.get_mut(&module_path).unwrap().constructors.insert(name.data.clone(), map);
            } else{
                self.interface.constructors.insert(name.data.clone(), map);
            }
        }
    }

    fn function_interface(&mut self, module_path: Option<Vec<Symbol>>, functions: &HashMap<Symbol, Function>) {
        for Function { name, params, ret, branches: _ } in functions.values() {
            let function_type = (
                params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect(),
                ret.as_ref().map_or(Type::Nothing, |ret| self.eval_type_expr(ret))
            );

            if let Some(module_path) = module_path.clone() {
                self.interface.imports.get_mut(&module_path).unwrap().functions.insert(name.data.clone(), function_type);
            } else{
                self.interface.functions.insert(name.data.clone(), function_type);
            }
        }
    }

    fn get_import_types(&mut self, Import { parts: _, kind, directs: _ }: &Import) {
        match kind {
            module::ImportKind::File((module, path)) => {
                // NOTE: Order here is important! (imports => types => constructors => functions)
                self.interface.imports.insert(vec![path.clone()], ImportTypes::default());

                self.import_interface(&module.imports);
                self.type_interface(Some(vec![path.clone()]), &module.types);
                self.constructor_interface(Some(vec![path.clone()]), &module.types);
                self.function_interface(Some(vec![path.clone()]), &module.functions);
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

#[derive(Default)]
pub struct Interface {
    functions: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
    imports: HashMap<Vec<Symbol>, ImportTypes>,
    types: HashMap<Symbol, typ::Type>,
    constructors: HashMap<Symbol, HashMap<Symbol, Vec<typ::Type>>>,
}

#[derive(Default, Debug)]
pub struct ImportTypes {
    functions: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
    types: HashMap<Symbol, typ::Type>,
    constructors: HashMap<Symbol, HashMap<Symbol, Vec<typ::Type>>>,
}

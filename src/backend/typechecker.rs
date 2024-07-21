use std::{collections::HashMap, fmt::Display, iter};

use crate::frontend::{span::{HasSpan, Span, Spanned}, token::Symbol};

use super::{
    ast::{
        AbsoluteBound, Application, Bound, ConstructorBound,
        Expression, Let, ModuleBound, Pattern, TypeExpression,
        TypeFunction
    },
    module::{self, Function, Import, Module},
    typ::{self, Type}
};

pub struct  TypeChecker {
    modules: HashMap<Symbol, Types>,
    locals: Vec<Type>,
}

impl TypeChecker {
    pub fn with_module(module: &Module) -> Self {
        let mut type_checker = Self {
            locals: Vec::new(),
            modules: HashMap::from([
                (module.path.clone(), Types::with_module(module))
            ]),
        };

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
            Bound::Absolute(abs_bound) => Ok(self.type_check_access(abs_bound)),
            Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
        }
    }

    fn type_check_application(&mut self, Application { expr, args }: &Application) -> TypeCheckResult<Type> {
        let typ = self.type_check_expr(expr)?;
        let Type::Function { vars, params, ret } = typ else {
            return Err(TypeCheckError::ExpectedFunction(typ).attach(expr.span()))
        };

        if args.len() != params.len() {
            return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: args.len() }.attach(expr.span()))
        }

        let table = if let Some(vars) = vars {
            self.initialize_type_var_table(vars, &params, args)?
        } else {
            Vec::new()
        };

        let params: Vec<_> = params
            .iter()
            .map(|param| Self::substitute_type(&table, param))
            .collect();

        for (arg, param) in iter::zip(args, params) {
            let typ = self.type_check_expr(arg)?;
            self.expect_type(&typ, &param, &arg.span())?;
        }

        Ok(Self::substitute_type(&table, &ret))
    }

    fn substitute_type(table: &[Type], typ: &Type) -> Type {
        match typ {
            Type::Function { vars, params, ret } => {
                if vars.is_none() {
                    typ.clone()
                } else {
                    let params = params
                        .iter()
                        .map(|param| Self::substitute_type(table, param))
                        .collect();
                    let ret = Box::new(Self::substitute_type(table, ret));
                    Type::Function { vars: None, params, ret }
                }
            },
            Type::Custom(vars, name) => {
                if vars.is_none() {
                    typ.clone()
                } else {
                    let mut table = table.to_vec();
                    table.reverse();
                    Type::Composite(name.clone(), table)
                }
            },
            Type::Variable(indice) => table[*indice].clone(),
            _ => typ.clone()
        }
    }

    fn initialize_type_var_table(&mut self, vars: Vec<Symbol>, params: &[Type], args: &[Expression]) -> TypeCheckResult<Vec<Type>> {
        let mut table = vec![];
        for var in 0..vars.len() {
            table.push(Type::Variable(var));
        }

        for (arg, param) in iter::zip(args, params) {
            match param {
                Type::Variable(indice) => {
                    if !matches!(table.get(*indice).unwrap(), Type::Variable(_)) {
                        continue;
                    }

                    let typ = self.type_check_expr(arg)?;
                    table[*indice] = typ;

                    if table.len() == vars.len() {
                        break;
                    }
                },
                _ => ()
            }
        }

        if table.len() != vars.len() {
            todo!("Unused type variable.")
        }

        Ok(table)
    }

    fn type_check_let(&mut self, Let { expr, type_expr, branches }: &Let) -> TypeCheckResult<Type> {
        // TODO: Check pattern exhaustiveness.
        let typ = if let Some(typ) = type_expr {
            let typ = self.eval_type_expr(typ);
            let expr_typ = self.type_check_expr(expr)?;
            self.expect_type(&expr_typ, &typ, &expr.span())?;
            expr_typ
        } else {
            self.type_check_expr(expr)?
        };

        let (first_pattern, first_body) = branches.first().unwrap();
        let local_count = self.define_pattern_types(first_pattern, &typ)?;
        let result = self.type_check_expr(&first_body)?;
        self.locals.truncate(self.locals.len() - local_count);

        for (pattern, body) in &branches[1..] {
            let local_count = self.define_pattern_types(pattern, &typ)?;
            let typ = self.type_check_expr(body)?;
            self.expect_type(&typ, &result, &body.span())?;
            self.locals.truncate(self.locals.len() - local_count);
            assert!(self.locals.is_empty())
        }

        Ok(result)
    }

    fn type_check_access(&self, abs_bound: &AbsoluteBound) -> Type {
        match abs_bound {
            AbsoluteBound::Module(ModuleBound { module, name }) => {
                let (params, ret) = (&self.modules[module].functions)[name].clone();
                // Polymorphic functions.
                Type::Function { vars: None, params, ret: Box::new(ret) }
            },
            AbsoluteBound::Constructor(ConstructorBound { module, typ, name }) => {
                let interface = &self.modules[module];
                // TODO: If constructor does not take any arguments, does not return a function type
                let ret = interface.types[typ].clone();
                let (vars, params) = interface.constructors[typ][name].clone();
                Type::Function { vars, params, ret: Box::new(ret) }
            }
            AbsoluteBound::Undetermined => unreachable!("Name Resolver must've resolved all access expressions."),
        }
    }

    fn define_pattern_types(&mut self, pattern: &Pattern, typ: &Type) -> TypeCheckResult<usize> {
        match (pattern, &typ) {
            (Pattern::Any(_), _) => {
                self.locals.push(typ.clone());
                Ok(1)
            },
            (Pattern::Constructor { abs_bound, params, .. }, Type::Composite(name, args)) => {
                let type_function = match abs_bound {
                    AbsoluteBound::Constructor(ConstructorBound { typ: typ_name, .. }) => {
                        if typ_name != name {
                            return Err(TypeCheckError::PatternMismatch(typ.clone()).attach(pattern.span()))
                        }

                        // inline
                        self.type_check_access(abs_bound)
                    },
                    _ => unreachable!()
                };

                let Type::Function { params: cparams, .. } = Self::substitute_type(args, &type_function) else {
                    unreachable!()
                };

                if cparams.len() != params.len() {
                    return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: cparams.len() }.attach(pattern.span()))
                }

                let mut local_count = 0;
                for (cparam, param) in iter::zip(cparams, params) {
                    local_count += self.define_pattern_types(param, &cparam)?;
                }

                Ok(local_count)
            }
            (Pattern::Constructor { params, abs_bound, .. }, Type::Custom(_vars, type_name)) => {
                let type_function = match abs_bound {
                    AbsoluteBound::Constructor(ConstructorBound { typ: typ_name, .. }) => {
                        if typ_name != type_name {
                            return Err(TypeCheckError::PatternMismatch(typ.clone()).attach(pattern.span()))
                        }

                        // inline
                        self.type_check_access(abs_bound)
                    },
                    _ => unreachable!()
                };

                let Type::Function { params: cparams, .. } = type_function else {
                    unreachable!()
                };

                if cparams.len() != params.len() {
                    return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: cparams.len() }.attach(pattern.span()))
                }

                let mut local_count = 0;
                for (cparam, param) in iter::zip(cparams, params) {
                    local_count += self.define_pattern_types(param, &cparam)?;
                }

                Ok(local_count)
            },
            (Pattern::String(_), Type::String)
            | (Pattern::Integer(_), Type::Integer)
            | (Pattern::Float(_), Type::Float) => Ok(0),
            _ => Err(TypeCheckError::PatternMismatch(typ.clone()).attach(pattern.span()))
        }
    }

    fn expect_type(&mut self, typ: &Type, expected: &Type, span: &Span) -> TypeCheckResult<()> {
        let found = typ.clone();
        match (&found, expected) {
            (Type::Variable(_), _) => (),
            (_, Type::Variable(_)) => (),
            (Type::Custom(_, type_name), Type::Composite(cname, _)) => if cname != type_name {
                return Err(TypeCheckError::TypeMismatch { expected: expected.clone(), found }.attach(span.clone()))
            },
            (Type::Composite(name1, args1), Type::Composite(name2, args2)) => {
                if name1 != name2 {
                    return Err(TypeCheckError::TypeMismatch { expected: expected.clone(), found }.attach(span.clone()))
                }

                for (arg1, arg2) in iter::zip(args1, args2) {
                    self.expect_type(arg1, arg2, span)?;
                }
            }
            (Type::Function { vars: vars1, params: params1, ret: ret1 },
             Type::Function { vars: vars2, params: params2, ret: ret2 }) => {
                assert!(vars1.is_none());
                assert!(vars2.is_none());

                for (param1, param2) in iter::zip(params1, params2) {
                    self.expect_type(param1, param2, span)?;
                }

                self.expect_type(ret1, ret2, span)?;
            }
            _ => if &found != expected {
                return Err(TypeCheckError::TypeMismatch { expected: expected.clone(), found }.attach(span.clone()))
            }
        }

        Ok(())
    }

    fn eval_type_expr(&mut self, type_expr: &TypeExpression) -> Type {
        match type_expr {
            TypeExpression::Identifier(_, bound, args) => self.eval_type_identifier(bound, args),
            TypeExpression::Function(type_function) => self.eval_type_function(type_function),
            TypeExpression::Access(_, abs_bound, args) => self.type_check_type_access(abs_bound, args),
        }
    }

    fn eval_type_identifier(&mut self, bound: &Bound, args: &Option<Vec<TypeExpression>>) -> Type {
        match bound {
            Bound::Local(indice) => Type::Variable(*indice),
            Bound::Absolute(abs_bound) => self.type_check_type_access(abs_bound, args),
            Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
        }
    }

    fn eval_type_function(&mut self, TypeFunction { params, ret }: &TypeFunction) -> Type {
        let params = params
            .iter()
            .map(|param| self.eval_type_expr(param))
            .collect();
        let ret = Box::new(self.eval_type_expr(ret));

        // TODO: Polymorphic functions
        Type::Function { vars: None, params, ret }
    }

    fn type_check_type_access(&mut self, abs_bound: &AbsoluteBound, args: &Option<Vec<TypeExpression>>) -> Type {
        let AbsoluteBound::Module(ModuleBound { module, name }) = abs_bound else {
            unreachable!()
        };

        let typ = self.modules[module].types[name].clone();

        if let Some(args) = args {
            match typ {
                Type::Custom(type_vars, name) => {
                    let args: Vec<_> = args.iter().map(|arg| self.eval_type_expr(arg)).collect();
                    if args.iter().all(|arg| matches!(arg, Type::Variable(_))) {
                        Type::Custom(type_vars, name)
                    } else {
                        Type::Composite(name, args)
                    }
                },
                _ => todo!("Non polymorphic type.")
            }
        } else {
            typ
        }
    }

    fn type_check_function(&mut self, module_path: &Symbol, Function { name, branches, .. }: &Function) -> TypeCheckResult<()> {
        let (params, ret) = self.modules[module_path].functions[&name.data].clone();

        for (patterns, body) in branches {
            if patterns.len() != params.len() {
                return Err(TypeCheckError::ArityMismatch { expected: params.len(), found: patterns.len() }.attach(name.span))
            }

            let mut local_count = 0;
            for (pattern, typ) in iter::zip(patterns, &params) {
                local_count += self.define_pattern_types(pattern, &typ)?;
            }

            let typ = self.type_check_expr(body)?;
            self.expect_type(&typ, &ret, &body.span())?;
            self.locals.truncate(self.locals.len() - local_count);
            assert!(self.locals.is_empty())
        }

        Ok(())
    }

    fn type_check_import(&mut self, Import { parts, kind, .. }: &Import) -> TypeCheckResult<()> {
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
            module::ImportKind::Folder((imports, _)) => {
                imports
                    .values()
                    .map(|import| self.type_check_import(import))
                    .collect::<Result<_, _>>()?
            },
        }

        Ok(())
    }

    fn type_interface(&mut self, module_path: &Symbol, types: &HashMap<Symbol, module::Type>) {
        for module::Type { type_vars, name, .. } in types.values() {
            let type_vars = type_vars.as_ref().map(|t| t
                .iter()
                .map(|var| var.data.clone())
                .collect::<Vec<_>>()
            );

            self.modules.get_mut(module_path).unwrap().types.insert(
                name.data.clone(),
                Type::Custom(type_vars, name.data.clone())
            );
        }
    }

    fn constructor_interface(&mut self, module_path: &Symbol, types: &HashMap<Symbol, module::Type>) {
        for module::Type { type_vars, name, consts, .. } in types.values() {
            let mut constructors = HashMap::with_capacity(consts.len());
            for (name, params) in consts {
                let params = params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect();

                let vars = type_vars.as_ref().map(|t| t
                    .iter()
                    .map(|var| var.data.clone())
                    .collect::<Vec<_>>()
                );

                constructors.insert(name.data.clone(), (vars, params));
            }

            self.modules.get_mut(module_path).unwrap().constructors.insert(
                name.data.clone(),
                constructors
            );
        }
    }

    fn function_interface(&mut self, module_path: &Symbol, functions: &HashMap<Symbol, Function>) {
        for Function { name, params, ret, .. } in functions.values() {
            let function_type = (
                params
                    .iter()
                    .map(|param| self.eval_type_expr(param))
                    .collect(),
                ret.as_ref().map_or(Type::Nothing, |ret| self.eval_type_expr(ret))
            );

            self.modules.get_mut(module_path).unwrap().functions.insert(
                name.data.clone(),
                function_type
            );
        }
    }

    fn get_import_types(&mut self, Import { kind, .. }: &Import) {
        match kind {
            module::ImportKind::File(module) => {
                if self.modules.contains_key(&module.path) {
                    // Already encountered the module.
                    return;
                }

                self.modules.insert(module.path.clone(), Types::with_module(module));
                // NOTE: Order here is important! (imports => types => constructors => functions)
                self.import_interface(&module.imports);
                self.type_interface(&module.path, &module.types);
                self.constructor_interface(&module.path, &module.types);
                self.function_interface(&module.path, &module.functions);
            },
            module::ImportKind::Folder((imports, _)) => self.import_interface(imports)
        }
    }

    fn import_interface(&mut self, imports: &HashMap<Symbol, Import>) {
        imports
            .values()
            .for_each(|import| self.get_import_types(import));
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

pub struct Types {
    functions: HashMap<Symbol, (Vec<typ::Type>, typ::Type)>,
    types: HashMap<Symbol, typ::Type>,
    constructors: HashMap<Symbol, HashMap<Symbol, (Option<Vec<Symbol>>, Vec<typ::Type>)>>,
}

impl Types {
    fn with_module(module: &Module) -> Self {
        Self {
            functions: HashMap::with_capacity(module.functions.len()),
            types: HashMap::with_capacity(module.types.len()),
            constructors: HashMap::with_capacity(module.types.len())
        }
    }
}

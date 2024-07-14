use std::{collections::HashMap, iter, rc::Rc};

use crate::frontend::token::Symbol;

use super::{
    ast::{
        AbsoluteBound, Application, Bound, ConstructorBound,
        Expression, Let, ModuleBound, Pattern
    },
    module::{self, Function, Import, Module},
    value::{FunctionInstance, FunctionValue, Value}
};

pub struct Evaluator {
    modules: HashMap<Symbol, Values>,
    locals: Vec<Value>
}

impl Evaluator {
    pub fn with_module(module: &Module) -> Self {
        let mut evaluator = Self {
            locals: Vec::new(),
            modules: HashMap::from([
                (module.path.clone(), Values::with_module(module))
            ])
        };

        evaluator.collect_functions(&module.path.clone(), &module.functions);
        evaluator.collect_imports(&module.imports);
        evaluator
    }

    pub fn eval_module_from_main(module: &Module) -> Value {
        let mut evaluator = Self::with_module(module);

        // TODO: Introduce entry point declaration.
        let function = evaluator.modules[&module.path].functions["main".into()].clone();
        let [branch] = &function.branches[..] else {
            todo!("Main function should only have 1 branch")
        };

        let result = evaluator.eval_expr(&branch.1);
        assert!(evaluator.locals.is_empty());
        result
    }

    pub fn eval_expr(&mut self, expr: &Expression) -> Value {
        match expr {
            Expression::Identifier(_, bound) => self.eval_identifier(bound),
            Expression::Integer(int) => Value::Integer(int.data.to_string().parse().unwrap()),
            Expression::Float(float) => Value::Float(float.data.to_string().parse().unwrap()),
            Expression::String(string) => Value::String(string.data.to_string()),
            Expression::Nothing(_) => Value::Nothing,
            Expression::Application(application) => self.eval_application(application),
            Expression::Let(lett) => self.eval_let(lett),
            Expression::Access(access) => self.eval_access(&access.abs_bound),
        }
    }

    fn eval_identifier(&self, bound: &Bound) -> Value {
        match bound {
            Bound::Local(indice) => self.locals[self.locals.len() - 1 - indice].clone(),
            Bound::Absolute(abs_bound) => self.eval_access(abs_bound),
            Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
        }
    }

    fn eval_let(&mut self, Let { expr, type_expr: _, branches }: &Let) -> Value {
        let value = self.eval_expr(expr);
        for (pattern, body) in branches {
            if Self::check_pattern(pattern, &value) {
                let local_count = self.define_pattern_values(pattern, value);
                let result = self.eval_expr(body);
                self.locals.truncate(self.locals.len() - local_count);
                assert!(self.locals.is_empty());
                return result
            }
        }

        unreachable!("Pattern must be exhaustive.")
    }

    fn eval_application(&mut self, Application { expr, args }: &Application) -> Value {
        match self.eval_expr(expr) {
            Value::Function(function) => self.eval_function_application(args, function),
            Value::Constructor(constructor) => self.eval_constructor_application(args, constructor),
            _ => unreachable!("Type Checker must've avoided non-applicable types in an application expression.")
        }
    }

    fn eval_function_application(&mut self, args: &[Expression], function: FunctionValue) -> Value {
        let values: Vec<_> = args
            .iter()
            .map(|arg| self.eval_expr(arg))
            .collect();

        for (patterns, body) in &function.branches {
            if !iter::zip(patterns, &values)
                .all(|(pattern, value)| Self::check_pattern(pattern, value))
            {
                continue;
            }

            let local_count: usize = iter::zip(patterns, values)
                .map(|(pattern, value)| self.define_pattern_values(&pattern, value))
                .sum();

            let result = self.eval_expr(&body);
            self.locals.truncate(self.locals.len() - local_count);
            return result;
        }

        unreachable!("Pattern must be exhaustive.")
    }

    fn eval_constructor_application(&mut self, args: &[Expression], constructor: Symbol) -> Value {
        let values = args
            .iter()
            .map(|arg| self.eval_expr(arg))
            .collect();

        Value::custom(constructor, values)
    }

    fn eval_access(&self, abs_bound: &AbsoluteBound) -> Value {
        match abs_bound {
            AbsoluteBound::Module(ModuleBound { module, name }) => Value::Function(self.modules[module].functions[name].clone()),
            AbsoluteBound::Constructor(ConstructorBound { name, .. }) => Value::Constructor(name.clone()),
            AbsoluteBound::Undetermined => unreachable!("Name Resolver must've resolved all access expressions."),
        }
    }

    fn check_pattern(pattern: &Pattern, value: &Value) -> bool {
        match (pattern, value) {
            (Pattern::Any(_), _) => true,
            (Pattern::String(pstr), Value::String(vstr)) => &*pstr.data == &vstr.clone(),
            (Pattern::Integer(pint), Value::Integer(vint)) => (&*pint.data).parse::<isize>().unwrap() == *vint,
            (Pattern::Float(pfloat), Value::Float(vfloat)) => (&*pfloat.data).parse::<f32>().unwrap() == *vfloat,
            (Pattern::Constructor { path, params, .. }, Value::Custom(custom)) => {
                &path.last().unwrap().data == &custom.constructor
                    &&
                iter::zip(params, &custom.values)
                    .all(|(param, value)| Self::check_pattern(param, value))
            },
            _ => false
        }
    }

    fn define_pattern_values(&mut self, pattern: &Pattern, value: Value) -> usize {
        match (pattern, value) {
            (Pattern::Any(_), value) => {
                self.locals.push(value);
                1
            },
            (Pattern::Constructor { params, .. }, Value::Custom(custom)) => {
                iter::zip(params, custom.values.clone())
                    .map(|(param, value)| self.define_pattern_values(&param, value))
                    .sum()
            },
            // NOTE: Type Checker guarantees that at this point we have
            //       literal patterns who does not introduce any new names.
            _ => 0
        }
    }

    fn collect_functions(&mut self, module_path: &Symbol, functions: &HashMap<Symbol, Function>) {
        for Function { name, branches, .. } in functions.values() {
            let function = Rc::new(FunctionInstance { branches: branches.to_vec() });
            self.modules.get_mut(module_path).unwrap().functions.insert(name.data.clone(), function);
        }
    }

    fn collect_import_values(&mut self, Import { kind, .. }: &Import) {
        match kind {
            module::ImportKind::File(module) => {
                if self.modules.contains_key(&module.path) {
                    // Already encountered the module.
                    return;
                }

                self.modules.insert(module.path.clone(), Values::with_module(module));
                self.collect_functions(&module.path, &module.functions);
                self.collect_imports(&module.imports);
            },
            module::ImportKind::Folder((imports, _)) => self.collect_imports(imports),
        }
    }

    fn collect_imports(&mut self, imports: &HashMap<Symbol, Import>) {
        imports
            .values()
            .for_each(|import| self.collect_import_values(import));
    }
}

struct Values {
    functions: HashMap<Symbol, FunctionValue>,
}

impl Values {
    fn with_module(module: &Module) -> Self {
        Self {
            functions: HashMap::with_capacity(module.functions.len())
        }
    }
}

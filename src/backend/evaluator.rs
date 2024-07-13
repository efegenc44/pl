use std::{collections::HashMap, iter};

use crate::frontend::token::Symbol;

use super::{ast::{AbsoluteBound, Application, Bound, ConstructorBound, Expression, Let, ModuleBound, Pattern}, module::{self, Function, Import, Module}, value::{FunctionValue, Value}};

pub struct Evaluator {
    modules: HashMap<Symbol, Values>,
    locals: Vec<Value>
}

impl Evaluator {
    pub fn new(module: &Module) -> Self {
        let mut evaluator = Self {
            locals: Vec::new(),
            modules: HashMap::new()
        };

        evaluator.modules.insert(module.path.clone(), Values::default());

        evaluator.collect_functions(&module.path.clone(), &module.functions);
        evaluator.collect_constructors(&module.path.clone(), &module.types);
        evaluator.collect_imports(&module.imports);
        evaluator
    }

    pub fn eval_module_from_main(module: &Module) -> Value {
        let mut evaluator = Self::new(module);

        // TODO: Checks on main should happen before probably at typechecking.
        let FunctionValue { branches } = evaluator.modules[&module.path].functions["main".into()].clone();
        let [branch] = &branches[..] else {
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
            // TODO: Remove to_vec
            Bound::Absolute(abs_bound) => self.eval_access(abs_bound),
            Bound::None => unreachable!("Name Resolver must've resolved all identifiers."),
        }
    }

    fn eval_let(&mut self, Let { expr, type_expr: _, branches }: &Let) -> Value {
        // Exhaustiveness check.

        let value = self.eval_expr(expr);
        for (pattern, body) in branches {
            if Self::check_pattern(pattern, &value) {
                let local_count = self.push_values_in_pattern(pattern, value);
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
            Value::Function(FunctionValue { branches }) => {
                let values: Vec<_> = args.iter().map(|arg| self.eval_expr(arg)).collect();

                'branch_loop: for (patterns, body) in branches {
                    for (pattern, arg) in iter::zip(&patterns, &values) {
                        if !Self::check_pattern(pattern, arg) {
                            continue 'branch_loop;
                        }
                    }

                    let mut local_count = 0;
                    for (pattern, arg) in iter::zip(patterns, values) {
                        local_count += self.push_values_in_pattern(&pattern, arg);
                    }

                    let result = self.eval_expr(&body);
                    self.locals.truncate(self.locals.len() - local_count);

                    return result;
                }

                unimplemented!("Pattern must be exhaustive.")
            }
            Value::Constructor(constructor, _) => {
                let values = args.iter().map(|arg| self.eval_expr(arg)).collect();
                Value::Custom { constructor, values }
            },
            _ => unreachable!()
        }
    }

    fn eval_access(&self, abs_bound: &AbsoluteBound) -> Value {
        match abs_bound {
            AbsoluteBound::Module(ModuleBound { module, name }) => {
                let function = self.modules[module].functions[name].clone();
                Value::Function(function)
            }
            AbsoluteBound::Constructor(ConstructorBound { module, typ, name }) => {
                let interface = &self.modules[module];
                // TODO: If constructor does not take any arguments, does not return a function type
                let arity = interface.constructors[typ][name].clone();
                Value::Constructor(name.clone(), arity)
            },
            AbsoluteBound::Undetermined => unreachable!(),
        }
    }

    fn check_pattern(pattern: &Pattern, value: &Value) -> bool {
        match (pattern, value) {
            (Pattern::Any(_), _) => true,
            (Pattern::String(str1), Value::String(str2)) => &str1.data == &str2.clone().into_boxed_str(),
            (Pattern::Integer(int1), Value::Integer(int2)) => &int1.data.to_string().parse::<isize>().unwrap() == int2,
            (Pattern::Float(float1), Value::Float(float2)) => &float1.data.to_string().parse::<f32>().unwrap() == float2,
            (Pattern::Constructor { path, params, abs_bound: _ }, Value::Custom { constructor, values }) => {
                if &path.last().unwrap().data != constructor {
                    return false;
                }

                for (param, value) in iter::zip(params, values) {
                    if !Self::check_pattern(param, value) {
                        return false
                    }
                }

                true
            },
            _ => false
        }
    }

    fn push_values_in_pattern(&mut self, pattern: &Pattern, value: Value) -> usize {
        match (pattern, value) {
            (Pattern::Any(_), value) => {
                self.locals.push(value);
                1
            },
            (Pattern::String(_), Value::String(_)) |
            (Pattern::Integer(_), Value::Integer(_)) |
            (Pattern::Float(_), Value::Float(_)) => 0,
            (Pattern::Constructor { path: _, params, abs_bound: _ }, Value::Custom { constructor: _, values }) => {
                let mut local_count = 0;
                for (param, value) in iter::zip(params, values) {
                    local_count += self.push_values_in_pattern(param, value);
                }

                local_count
            },
            _ => unreachable!()
        }
    }

    fn collect_functions(&mut self, module_path: &Symbol, functions: &HashMap<Symbol, Function>) {
        for Function { name, branches, .. } in functions.values() {
            self.modules.get_mut(module_path).unwrap().functions.insert(name.data.clone(), FunctionValue { branches: branches.to_vec() });
        }
    }

    fn collect_constructors(&mut self, module_path: &Symbol, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts } in types.values() {
            let mut map = HashMap::new();
            for (name, params) in consts {
                let params = params.len();
                map.insert(name.data.clone(), params);
            }

            self.modules.get_mut(module_path).unwrap().constructors.insert(name.data.clone(), map);
        }
    }

    fn get_import_values(&mut self, Import { parts: _, kind, directs: _ }: &Import) {
        match kind {
            module::ImportKind::File(module) => {
                if self.modules.contains_key(&module.path) {
                    // already encountered the module.
                    return;
                }

                self.modules.insert(module.path.clone(), Values::default());

                self.collect_functions(&module.path, &module.functions);
                self.collect_constructors(&module.path, &module.types);
                self.collect_imports(&module.imports);
            },
            module::ImportKind::Folder((imports, _path)) => {
                self.collect_imports(imports);
            },
        }
    }

    fn collect_imports(&mut self, imports: &HashMap<Symbol, Import>) {
        for (_, import) in imports {
            self.get_import_values(import);
        }
    }
}

#[derive(Debug, Default)]
struct Values {
    functions: HashMap<Symbol, FunctionValue>,
    constructors: HashMap<Symbol, HashMap<Symbol, usize>>,
}

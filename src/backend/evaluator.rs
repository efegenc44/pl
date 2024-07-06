use std::{collections::HashMap, iter};

use crate::frontend::token::Symbol;

use super::{ast::{Access, Application, Bound, Expression, Let, Namespace, Pattern}, module::{self, Function, Import, Module}, value::{FunctionValue, Value}};

pub struct Evaluator {
    values: Values,
    locals: Vec<Value>
}

impl Evaluator {
    pub fn new(module: &Module) -> Self {
        let mut evaluator = Self { locals: Vec::new(), values: Values::default() };

        evaluator.collect_functions(None, &module.functions);
        evaluator.collect_constructors(None, &module.types);
        evaluator.collect_imports(&module.imports);
        evaluator
    }

    pub fn eval_module_from_main(module: &Module) -> Value {
        let mut evaluator = Self::new(module);

        // TODO: Checks on main should happen before probably at typechecking.
        let FunctionValue { branches } = evaluator.values.functions["main".into()].clone();
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
            Expression::Binary(_) => todo!("Evaluation of binary expressions"),
            Expression::Application(application) => self.eval_application(application),
            Expression::Let(lett) => self.eval_let(lett),
            Expression::Lambda(_) => todo!("Evaluation of lambdas"),
            Expression::Access(access) => self.eval_access(access),
        }
    }

    fn eval_identifier(&self, bound: &Bound) -> Value {
        match bound {
            Bound::Local(indice) => self.locals[self.locals.len() - 1 - indice].clone(),
            Bound::Global(identifier) =>  Value::Function(self.values.functions[identifier].clone()),
            // TODO: Remove to_vec
            Bound::Absolute(path) => self.eval_access(&Access { path: path.to_vec(), namespace: Namespace::Module }),
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

    fn eval_access(&self, Access { path, namespace }: &Access) -> Value {
        match &path[..] {
            [_] | [] => unreachable!(),
            [a@.., from, name] => {
                match namespace {
                    Namespace::Type => {
                        if a.is_empty() {
                            // TODO: If constructor does not take any arguments, does not return a function type
                            let arity = self.values.constructors[&from.data][&name.data].clone();
                            Value::Constructor(name.data.clone(), arity)
                        } else {
                            let interface = &self.values.imports[&a.last().unwrap().data];
                            // TODO: If constructor does not take any arguments, does not return a function type
                            let arity = interface.constructors[&from.data][&name.data].clone();
                            Value::Constructor(name.data.clone(), arity)
                        }

                    }
                    Namespace::Module => {
                        let function = (&self.values.imports[&from.data].functions)[&name.data].clone();
                        Value::Function(function)
                    },
                    Namespace::Undetermined => unreachable!(),
                }
            }
        }
    }

    fn check_pattern(pattern: &Pattern, value: &Value) -> bool {
        match (pattern, value) {
            (Pattern::Any(_), _) => true,
            (Pattern::String(str1), Value::String(str2)) => &str1.data == &str2.clone().into_boxed_str(),
            (Pattern::Integer(int1), Value::Integer(int2)) => &int1.data.to_string().parse::<isize>().unwrap() == int2,
            (Pattern::Float(float1), Value::Float(float2)) => &float1.data.to_string().parse::<f32>().unwrap() == float2,
            (Pattern::Constructor { path, params }, Value::Custom { constructor, values }) => {
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
            (Pattern::Constructor { path: _, params }, Value::Custom { constructor: _, values }) => {
                let mut local_count = 0;
                for (param, value) in iter::zip(params, values) {
                    local_count += self.push_values_in_pattern(param, value);
                }

                local_count
            },
            _ => unreachable!()
        }
    }

    fn collect_functions(&mut self, module_name: Option<Symbol>, functions: &HashMap<Symbol, Function>) {
        for Function { name, branches, .. } in functions.values() {
            if let Some(module_name) = module_name.clone() {
                self.values.imports.get_mut(&module_name).unwrap().functions.insert(name.data.clone(), FunctionValue { branches: branches.to_vec() });
            } else{
                self.values.functions.insert(name.data.clone(), FunctionValue { branches: branches.to_vec() });
            }
        }
    }

    fn collect_constructors(&mut self, module_name: Option<Symbol>, types: &HashMap<Symbol, module::Type>) {
        for module::Type { name, consts } in types.values() {
            let mut map = HashMap::new();
            for (name, params) in consts {
                let params = params.len();
                map.insert(name.data.clone(), params);
            }

            if let Some(module_name) = module_name.clone() {
                self.values.imports.get_mut(&module_name).unwrap().constructors.insert(name.data.clone(), map);
            } else{
                self.values.constructors.insert(name.data.clone(), map);
            }
        }
    }

    fn get_import_values(&mut self, name: Symbol, Import { parts: _, kind, directs: _ }: &Import) {
        match kind {
            module::ImportKind::File(module) => {
                self.values.imports.insert(name.clone(), ImportValues::default());

                self.collect_functions(Some(name.clone()), &module.functions);
                self.collect_constructors(Some(name.clone()), &module.types);
                self.collect_imports(&module.imports);
            },
            module::ImportKind::Folder(imports) => {
                self.collect_imports(imports);
            },
        }
    }

    fn collect_imports(&mut self, imports: &HashMap<Symbol, Import>) {
        for (name, import) in imports {
            self.get_import_values(name.clone(), import);
        }
    }
}

#[derive(Default)]
pub struct Values {
    functions: HashMap<Symbol, FunctionValue>,
    imports: HashMap<Symbol, ImportValues>,
    constructors: HashMap<Symbol, HashMap<Symbol, usize>>,
}

#[derive(Debug, Default)]
struct ImportValues {
    functions: HashMap<Symbol, FunctionValue>,
    constructors: HashMap<Symbol, HashMap<Symbol, usize>>,
}

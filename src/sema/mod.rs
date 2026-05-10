use std::collections::HashMap;

use crate::ast::Expr;

pub type Env = HashMap<String, i32>;

/// Evaluate a JS expression under the given environment.
/// Uses wrapping arithmetic to match WASM i32 semantics.
pub fn eval_js(e: &Expr, env: &Env) -> i32 {
    match e {
        Expr::Num(n) => *n,
        Expr::Var(x) => *env.get(x).expect("unbound variable"),
        Expr::Add(a, b) => eval_js(a, env).wrapping_add(eval_js(b, env)),
        Expr::Sub(a, b) => eval_js(a, env).wrapping_sub(eval_js(b, env)),
        Expr::Mul(a, b) => eval_js(a, env).wrapping_mul(eval_js(b, env)),
        Expr::Let(x, val, body) => {
            let v = eval_js(val, env);
            let mut env2 = env.clone();
            env2.insert(x.clone(), v);
            eval_js(body, &env2)
        }
    }
}

/// Batch/parallel semantics: evaluate expression `e` for each input in `inputs`.
/// Each input maps the variable "x" to a different value.
/// This is the reference semantics for the CUDA backend:
///   eval_parallel(e, inputs) = inputs.map(|x| eval_js(e, {"x": x}))
pub fn eval_parallel(e: &Expr, inputs: &[i32]) -> Vec<i32> {
    inputs
        .iter()
        .map(|&x| {
            let mut env = Env::new();
            env.insert("x".to_string(), x);
            eval_js(e, &env)
        })
        .collect()
}

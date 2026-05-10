use std::collections::HashMap;

use c11_wasm::ast::Expr;
use c11_wasm::codegen::cuda::{compile_cuda, eval_cuda};
use c11_wasm::codegen::{compile, emit_wasm, eval_wasm};
use c11_wasm::sema::{eval_js, eval_parallel};

use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn empty_env() -> HashMap<String, i32> {
    HashMap::new()
}

/// Run compiled WASM bytes through wasmtime and return the i32 result.
fn run_wasm(bytes: &[u8]) -> i32 {
    use wasmtime::*;
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();
    let main = instance.get_typed_func::<(), i32>(&mut store, "main").unwrap();
    main.call(&mut store, ()).unwrap()
}

/// Three-way correctness check: eval_js == eval_wasm (our interpreter) == wasmtime (real WASM)
fn assert_full_correctness(e: &Expr) {
    let env = empty_env();
    let js = eval_js(e, &env);
    let compiled = compile(e);
    let ours = eval_wasm(&compiled);
    let wasm_bytes = emit_wasm(&compiled);
    let real = run_wasm(&wasm_bytes);

    assert_eq!(js, ours, "eval_js != eval_wasm");
    assert_eq!(js, real, "eval_js != wasmtime");
}

// ---------------------------------------------------------------------------
// Hand-written unit tests
// ---------------------------------------------------------------------------

#[test]
fn correctness_num() {
    assert_full_correctness(&Expr::num(42));
}

#[test]
fn correctness_add() {
    assert_full_correctness(&Expr::add(Expr::num(1), Expr::num(2)));
}

#[test]
fn correctness_sub() {
    assert_full_correctness(&Expr::sub(Expr::num(10), Expr::num(3)));
}

#[test]
fn correctness_mul() {
    assert_full_correctness(&Expr::mul(Expr::num(6), Expr::num(7)));
}

#[test]
fn correctness_nested_arith() {
    // (1 + 2) * (3 - 4)
    let e = Expr::mul(
        Expr::add(Expr::num(1), Expr::num(2)),
        Expr::sub(Expr::num(3), Expr::num(4)),
    );
    assert_full_correctness(&e);
}

#[test]
fn correctness_let_simple() {
    // let x = 5 in x + 1
    let e = Expr::let_("x", Expr::num(5), Expr::add(Expr::var("x"), Expr::num(1)));
    assert_full_correctness(&e);
}

#[test]
fn correctness_let_nested() {
    // let x = 3 + 4 in let y = x * 2 in x + y
    let e = Expr::let_(
        "x",
        Expr::add(Expr::num(3), Expr::num(4)),
        Expr::let_(
            "y",
            Expr::mul(Expr::var("x"), Expr::num(2)),
            Expr::add(Expr::var("x"), Expr::var("y")),
        ),
    );
    assert_full_correctness(&e);
}

#[test]
fn correctness_let_shadow() {
    // let x = 1 in let x = x + 10 in x
    let e = Expr::let_(
        "x",
        Expr::num(1),
        Expr::let_(
            "x",
            Expr::add(Expr::var("x"), Expr::num(10)),
            Expr::var("x"),
        ),
    );
    assert_full_correctness(&e);
    assert_eq!(eval_js(&e, &empty_env()), 11);
}

#[test]
fn correctness_overflow_wrapping() {
    // i32::MAX + 1 should wrap
    let e = Expr::add(Expr::num(i32::MAX), Expr::num(1));
    assert_full_correctness(&e);
}

#[test]
fn correctness_negative() {
    assert_full_correctness(&Expr::add(Expr::num(-10), Expr::num(3)));
}

#[test]
fn correctness_deep() {
    // ((1 + 2) + 3) + (4 + (5 + 6))
    let e = Expr::add(
        Expr::add(Expr::add(Expr::num(1), Expr::num(2)), Expr::num(3)),
        Expr::add(Expr::num(4), Expr::add(Expr::num(5), Expr::num(6))),
    );
    assert_full_correctness(&e);
    assert_eq!(eval_js(&e, &empty_env()), 21);
}

// ---------------------------------------------------------------------------
// Property-based tests (proptest)
// ---------------------------------------------------------------------------

/// Generate a well-scoped Expr tree. `bound` tracks variables in scope.
fn arb_expr(bound: Vec<String>, depth: u32) -> BoxedStrategy<Expr> {
    if depth == 0 {
        // Leaf: Num or Var (if any variables are bound)
        let mut leaves: Vec<BoxedStrategy<Expr>> =
            vec![(-1000i32..1000).prop_map(Expr::num).boxed()];
        if !bound.is_empty() {
            let vars = bound.clone();
            leaves.push(
                (0..vars.len())
                    .prop_map(move |i| Expr::Var(vars[i].clone()))
                    .boxed(),
            );
        }
        proptest::strategy::Union::new(leaves).boxed()
    } else {
        let bv = bound.clone();

        // Binary arithmetic ops
        let binop = {
            let bv = bv.clone();
            (
                arb_expr(bv.clone(), depth - 1),
                arb_expr(bv, depth - 1),
                0u8..3,
            )
                .prop_map(|(a, b, op)| match op {
                    0 => Expr::add(a, b),
                    1 => Expr::sub(a, b),
                    _ => Expr::mul(a, b),
                })
                .boxed()
        };

        // Let binding: introduces a new variable
        let var_name = format!("v{}", bound.len());
        let let_strat = {
            let vn = var_name.clone();
            let bv2 = bv.clone();
            let mut new_bound = bound.clone();
            new_bound.push(var_name);
            (
                arb_expr(bv2, depth - 1),
                arb_expr(new_bound, depth - 1),
            )
                .prop_map(move |(val, body)| Expr::let_(&vn, val, body))
                .boxed()
        };

        // Leaf cases (to avoid always recursing)
        let num = (-1000i32..1000).prop_map(Expr::num).boxed();

        let mut choices = vec![binop, let_strat, num];
        if !bound.is_empty() {
            let vars = bound.clone();
            choices.push(
                (0..vars.len())
                    .prop_map(move |i| Expr::Var(vars[i].clone()))
                    .boxed(),
            );
        }

        proptest::strategy::Union::new(choices).boxed()
    }
}

// ---------------------------------------------------------------------------
// CUDA backend tests
// ---------------------------------------------------------------------------

/// Assert that CUDA parallel evaluation matches sequential eval_js for all inputs.
fn assert_cuda_correctness(e: &Expr, inputs: &[i32]) {
    let sequential = eval_parallel(e, inputs);
    let parallel = eval_cuda(e, inputs);
    assert_eq!(sequential, parallel, "eval_parallel != eval_cuda");
}

#[test]
fn cuda_simple_identity() {
    // f(x) = x
    assert_cuda_correctness(&Expr::var("x"), &[1, 2, 3, 0, -1]);
}

#[test]
fn cuda_constant() {
    // f(x) = 42
    assert_cuda_correctness(&Expr::num(42), &[1, 2, 3]);
}

#[test]
fn cuda_arithmetic() {
    // f(x) = x * x + 1
    let e = Expr::add(
        Expr::mul(Expr::var("x"), Expr::var("x")),
        Expr::num(1),
    );
    assert_cuda_correctness(&e, &[-3, -2, -1, 0, 1, 2, 3]);
}

#[test]
fn cuda_let_binding() {
    // f(x) = let y = x + 1 in y * y
    let e = Expr::let_(
        "y",
        Expr::add(Expr::var("x"), Expr::num(1)),
        Expr::mul(Expr::var("y"), Expr::var("y")),
    );
    assert_cuda_correctness(&e, &[0, 1, 2, 3, 10, -5]);
}

#[test]
fn cuda_nested_let() {
    // f(x) = let a = x * 2 in let b = a + 3 in a * b
    let e = Expr::let_(
        "a",
        Expr::mul(Expr::var("x"), Expr::num(2)),
        Expr::let_(
            "b",
            Expr::add(Expr::var("a"), Expr::num(3)),
            Expr::mul(Expr::var("a"), Expr::var("b")),
        ),
    );
    assert_cuda_correctness(&e, &[0, 1, 2, 5, -1, 100]);
}

#[test]
fn cuda_overflow_wrapping() {
    // f(x) = x + 2147483647 (should wrap)
    let e = Expr::add(Expr::var("x"), Expr::num(i32::MAX));
    assert_cuda_correctness(&e, &[0, 1, 2, -1]);
}

#[test]
fn cuda_empty_inputs() {
    assert_cuda_correctness(&Expr::var("x"), &[]);
}

#[test]
fn cuda_kernel_generation() {
    // Verify kernel source is generated and contains expected structure
    let e = Expr::add(Expr::var("x"), Expr::num(1));
    let kernel = compile_cuda(&e);
    assert!(kernel.source.contains("__global__"));
    assert!(kernel.source.contains("eval_kernel"));
    assert!(kernel.source.contains("inputs[idx]"));
    assert!(kernel.source.contains("outputs[idx]"));
}

// ---------------------------------------------------------------------------
// Property-based tests
// ---------------------------------------------------------------------------

/// Generate an Expr tree using only "x" as a free variable (for CUDA batch tests).
fn arb_cuda_expr(depth: u32) -> BoxedStrategy<Expr> {
    if depth == 0 {
        prop_oneof![
            (-1000i32..1000).prop_map(Expr::num),
            Just(Expr::Var("x".to_string())),
        ]
        .boxed()
    } else {
        prop_oneof![
            (-1000i32..1000).prop_map(Expr::num),
            Just(Expr::Var("x".to_string())),
            (arb_cuda_expr(depth - 1), arb_cuda_expr(depth - 1), 0u8..3)
                .prop_map(|(a, b, op)| match op {
                    0 => Expr::add(a, b),
                    1 => Expr::sub(a, b),
                    _ => Expr::mul(a, b),
                }),
            (
                arb_cuda_expr(depth - 1),
                arb_cuda_expr(depth - 1),
            )
                .prop_map(|(val, body)| Expr::let_("y", val, body)),
        ]
        .boxed()
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// The core correctness property: for ALL well-scoped expressions,
    /// eval_wasm(compile(e)) == eval_js(e, {}).
    /// This is the computational analogue of the inductive proof.
    #[test]
    fn prop_eval_wasm_eq_eval_js(e in arb_expr(vec![], 4)) {
        let env = empty_env();
        let js = eval_js(&e, &env);
        let compiled = compile(&e);
        let ours = eval_wasm(&compiled);
        prop_assert_eq!(ours, js, "eval_wasm != eval_js for {:?}", e);
    }

    /// Three-way property: eval_js == eval_wasm == wasmtime (real WASM engine).
    /// This validates our WASM emission against a production WASM runtime.
    #[test]
    fn prop_three_way_correctness(e in arb_expr(vec![], 3)) {
        let env = empty_env();
        let js = eval_js(&e, &env);
        let compiled = compile(&e);
        let ours = eval_wasm(&compiled);
        let wasm_bytes = emit_wasm(&compiled);
        let real = run_wasm(&wasm_bytes);
        prop_assert_eq!(js, ours, "eval_js != eval_wasm for {:?}", e);
        prop_assert_eq!(js, real, "eval_js != wasmtime for {:?}", e);
    }

    /// CUDA batch correctness: eval_cuda(e, inputs) == eval_parallel(e, inputs)
    /// for random expressions and random input batches.
    #[test]
    fn prop_cuda_batch_correctness(
        e in arb_cuda_expr(3),
        inputs in proptest::collection::vec(-1000i32..1000, 0..20),
    ) {
        let sequential = eval_parallel(&e, &inputs);
        let parallel = eval_cuda(&e, &inputs);
        prop_assert_eq!(sequential, parallel,
            "eval_parallel != eval_cuda for {:?} with inputs {:?}", e, inputs);
    }
}

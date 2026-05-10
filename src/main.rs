mod ast;
mod codegen;
mod hir;
mod lexer;
mod mir;
mod parser;
mod sema;

use ast::Expr;
use codegen::cuda::{compile_cuda, eval_cuda};
use codegen::{compile, emit_wasm, eval_wasm};
use sema::{eval_js, eval_parallel};
use std::collections::HashMap;

fn main() {
    // ── WASM path ──
    // let x = 3 + 4 in let y = x * 2 in x + y
    let expr = Expr::let_(
        "x",
        Expr::add(Expr::num(3), Expr::num(4)),
        Expr::let_(
            "y",
            Expr::mul(Expr::var("x"), Expr::num(2)),
            Expr::add(Expr::var("x"), Expr::var("y")),
        ),
    );

    let env = HashMap::new();
    let js_result = eval_js(&expr, &env);
    let compiled = compile(&expr);
    let wasm_result = eval_wasm(&compiled);
    let wasm_bytes = emit_wasm(&compiled);

    println!("=== WASM Backend ===");
    println!("Expression: let x = 3 + 4 in let y = x * 2 in x + y");
    println!("eval_js    = {}", js_result);
    println!("eval_wasm  = {}", wasm_result);
    println!("WASM size  = {} bytes", wasm_bytes.len());
    println!("Instructions: {:?}", compiled.instrs);
    assert_eq!(js_result, wasm_result);
    println!("Correctness: eval_wasm(compile(e)) == eval_js(e)");

    // ── CUDA path ──
    // Batch evaluate: x * x + 1 for inputs [1, 2, 3, 4, 5]
    let cuda_expr = Expr::add(
        Expr::mul(Expr::var("x"), Expr::var("x")),
        Expr::num(1),
    );
    let inputs = vec![1, 2, 3, 4, 5];

    let sequential = eval_parallel(&cuda_expr, &inputs);
    let parallel = eval_cuda(&cuda_expr, &inputs);
    let kernel = compile_cuda(&cuda_expr);

    println!("\n=== CUDA Backend ===");
    println!("Expression: x * x + 1");
    println!("Inputs:     {:?}", inputs);
    println!("eval_parallel = {:?}", sequential);
    println!("eval_cuda     = {:?}", parallel);
    assert_eq!(sequential, parallel);
    println!("Correctness: eval_cuda(compile_cuda(e), inputs) == eval_parallel(e, inputs)");
    println!("\nGenerated CUDA kernel:");
    println!("{}", kernel.source);
}

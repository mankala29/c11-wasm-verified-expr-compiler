pub mod cuda;

use std::collections::HashMap;

use crate::ast::Expr;
use crate::mir::{WasmFunc, WasmInstr};

struct CompileCtx {
    locals: HashMap<String, u32>,
    next_local: u32,
}

/// Compile an Expr to a WASM function (stack-based instructions + locals).
pub fn compile(e: &Expr) -> WasmFunc {
    let mut ctx = CompileCtx {
        locals: HashMap::new(),
        next_local: 0,
    };
    let instrs = compile_expr(e, &mut ctx);
    WasmFunc {
        num_locals: ctx.next_local,
        instrs,
    }
}

fn compile_expr(e: &Expr, ctx: &mut CompileCtx) -> Vec<WasmInstr> {
    match e {
        Expr::Num(n) => vec![WasmInstr::I32Const(*n)],
        Expr::Var(x) => {
            let idx = *ctx.locals.get(x).expect("unbound variable during compilation");
            vec![WasmInstr::LocalGet(idx)]
        }
        Expr::Add(a, b) => {
            let mut out = compile_expr(a, ctx);
            out.extend(compile_expr(b, ctx));
            out.push(WasmInstr::I32Add);
            out
        }
        Expr::Sub(a, b) => {
            let mut out = compile_expr(a, ctx);
            out.extend(compile_expr(b, ctx));
            out.push(WasmInstr::I32Sub);
            out
        }
        Expr::Mul(a, b) => {
            let mut out = compile_expr(a, ctx);
            out.extend(compile_expr(b, ctx));
            out.push(WasmInstr::I32Mul);
            out
        }
        Expr::Let(x, val, body) => {
            let idx = ctx.next_local;
            ctx.next_local += 1;
            // Compile val BEFORE updating locals — val sees the outer scope
            let mut out = compile_expr(val, ctx);
            out.push(WasmInstr::LocalSet(idx));
            let old = ctx.locals.insert(x.clone(), idx);
            out.extend(compile_expr(body, ctx));
            // Restore previous binding (handles shadowing)
            match old {
                Some(old_idx) => {
                    ctx.locals.insert(x.clone(), old_idx);
                }
                None => {
                    ctx.locals.remove(x);
                }
            }
            out
        }
    }
}

/// Evaluate compiled WASM instructions on a stack machine.
/// This is our "eval_wasm" — the target semantics.
pub fn eval_wasm(func: &WasmFunc) -> i32 {
    let mut stack: Vec<i32> = Vec::new();
    let mut locals: Vec<i32> = vec![0; func.num_locals as usize];

    for instr in &func.instrs {
        match instr {
            WasmInstr::I32Const(n) => stack.push(*n),
            WasmInstr::I32Add => {
                let b = stack.pop().expect("stack underflow");
                let a = stack.pop().expect("stack underflow");
                stack.push(a.wrapping_add(b));
            }
            WasmInstr::I32Sub => {
                let b = stack.pop().expect("stack underflow");
                let a = stack.pop().expect("stack underflow");
                stack.push(a.wrapping_sub(b));
            }
            WasmInstr::I32Mul => {
                let b = stack.pop().expect("stack underflow");
                let a = stack.pop().expect("stack underflow");
                stack.push(a.wrapping_mul(b));
            }
            WasmInstr::LocalGet(idx) => stack.push(locals[*idx as usize]),
            WasmInstr::LocalSet(idx) => {
                let v = stack.pop().expect("stack underflow");
                locals[*idx as usize] = v;
            }
        }
    }

    stack.pop().expect("empty stack after execution")
}

/// Emit a real WASM binary module using wasm-encoder.
pub fn emit_wasm(func: &WasmFunc) -> Vec<u8> {
    use wasm_encoder::*;

    let mut module = Module::new();

    // Type section: () -> i32
    let mut types = TypeSection::new();
    types.ty().function(vec![], vec![ValType::I32]);
    module.section(&types);

    // Function section
    let mut functions = FunctionSection::new();
    functions.function(0);
    module.section(&functions);

    // Export section
    let mut exports = ExportSection::new();
    exports.export("main", ExportKind::Func, 0);
    module.section(&exports);

    // Code section
    let mut codes = CodeSection::new();
    let locals = if func.num_locals > 0 {
        vec![(func.num_locals, ValType::I32)]
    } else {
        vec![]
    };
    let mut f = Function::new(locals);
    for instr in &func.instrs {
        match instr {
            WasmInstr::I32Const(n) => {
                f.instruction(&Instruction::I32Const(*n));
            }
            WasmInstr::I32Add => {
                f.instruction(&Instruction::I32Add);
            }
            WasmInstr::I32Sub => {
                f.instruction(&Instruction::I32Sub);
            }
            WasmInstr::I32Mul => {
                f.instruction(&Instruction::I32Mul);
            }
            WasmInstr::LocalGet(idx) => {
                f.instruction(&Instruction::LocalGet(*idx));
            }
            WasmInstr::LocalSet(idx) => {
                f.instruction(&Instruction::LocalSet(*idx));
            }
        }
    }
    f.instruction(&Instruction::End);
    codes.function(&f);
    module.section(&codes);

    module.finish()
}

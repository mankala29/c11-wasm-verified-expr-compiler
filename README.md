# c11-wasm: A Verified Expression Compiler

A small expression compiler with **two backends** (WASM + CUDA) and a **machine-checked correctness proof** in Lean 4. Zero sorry. Zero axioms. Kernel-checked.

Inspired by [Basis's experiment](https://basis.ai/blog/building-an-unverified-compiler-with-agents/) where 4 AI agents wrote 93k lines of Lean over 14 days attempting a verified JS-to-WASM compiler — and couldn't close a single non-trivial proof. This project takes the opposite approach: constrain the language, close the proofs.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      SOURCE EXPRESSION                       │
│           Expr { Num, Var, Add, Sub, Mul, Let }              │
│                        (src/ast)                             │
└──────────────────┬──────────────────────┬────────────────────┘
                   │                      │
                   ▼                      ▼
┌────────────────────────┐   ┌────────────────────────────────┐
│  REFERENCE SEMANTICS   │   │       COMPILER BACKENDS         │
│      (src/sema)        │   │                                 │
│                        │   │  ┌──────────┐  ┌────────────┐  │
│  eval_js(e, env)       │   │  │   WASM   │  │    CUDA    │  │
│    -> i32              │   │  │ codegen/ │  │  codegen/  │  │
│                        │   │  │ mod.rs   │  │  cuda.rs   │  │
│  eval_parallel(e,      │   │  └────┬─────┘  └──────┬─────┘  │
│    inputs) -> Vec      │   │       │               │         │
└────────┬───────────────┘   └───────┼───────────────┼─────────┘
         │                           │               │
         │                           ▼               ▼
         │                ┌────────────────┐  ┌────────────────┐
         │                │   WasmFunc     │  │  CudaKernel    │
         │                │   (src/mir)    │  │  .source       │
         │                │   i32.const    │  │  __global__    │
         │                │   i32.add      │  │  eval_kernel   │
         │                │   local.get    │  │                │
         │                │   local.set    │  │                │
         │                └───────┬────────┘  └───────┬────────┘
         │                        │                   │
         │               ┌───────┴──────┐             │
         │               ▼              ▼             ▼
         │        ┌────────────┐ ┌───────────┐ ┌────────────┐
         │        │ eval_wasm  │ │ emit_wasm │ │ eval_cuda  │
         │        │ (interp)   │ │ (binary)  │ │ (CPU sim)  │
         │        │  -> i32    │ │ -> bytes  │ │ -> Vec     │
         │        └─────┬──────┘ └─────┬─────┘ └─────┬──────┘
         │              │              │              │
         ▼              ▼              ▼              ▼
┌──────────────────────────────────────────────────────────────┐
│                     VERIFICATION LAYER                        │
│                                                              │
│  ┌──────────────────────────────┐  ┌──────────────────────┐  │
│  │    FORMAL PROOF (Lean 4)     │  │   EMPIRICAL TESTS    │  │
│  │  proofs/Leanproof/           │  │  tests/integration   │  │
│  │  Correctness.lean            │  │                      │  │
│  │                              │  │  proptest (500x):    │  │
│  │  compile_correct:            │  │   eval_js ==         │  │
│  │   eval_js(e) = v  =>        │  │   eval_wasm ==       │  │
│  │   exec(compile(e)) = [v]    │  │   wasmtime           │  │
│  │                              │  │                      │  │
│  │  eval_parallel_correct:      │  │  proptest (500x):    │  │
│  │   batch = map(sequential)   │  │   eval_parallel ==   │  │
│  │                              │  │   eval_cuda          │  │
│  │  0 sorry | 0 axioms         │  │                      │  │
│  └──────────────────────────────┘  └──────────────────────┘  │
│                                                              │
│  PROVES: Lean model correct     VALIDATES: Rust impl         │
│  (design can't be wrong)        (impl matches design)        │
└──────────────────────────────────────────────────────────────┘
```

### Correctness Relationships

```
  eval_js(e, env) ══════╗
       ║                ║
       ║ Lean proof     ║ proptest
       ║ (mathematical) ║ (empirical)
       ▼                ▼
  exec(compile(e)) == eval_wasm(compile(e)) == wasmtime(emit_wasm)

  eval_parallel(e, inputs) ══════╗
       ║                         ║
       ║ Lean proof (rfl)        ║ proptest
       ║                         ▼
       ╚═══ map(eval_js) ══ eval_cuda(e, inputs)
```

### Data Flow

```
  WASM path:
    Expr -> compile() -> WasmFunc -> eval_wasm()  -> i32
                                  -> emit_wasm()  -> .wasm bytes -> wasmtime

  CUDA path:
    Expr -> compile_cuda() -> CudaKernel (.source)
    Expr -> eval_cuda(inputs) -> Vec<i32>   (CPU simulation)

  Reference:
    Expr -> eval_js(env)            -> i32
    Expr -> eval_parallel(inputs)   -> Vec<i32>
```

## Module Structure

```
  src/
  ├── ast/mod.rs       Expr type (Num, Var, Add, Sub, Mul, Let)
  ├── sema/mod.rs      eval_js, eval_parallel (reference semantics)
  ├── codegen/
  │   ├── mod.rs       compile, eval_wasm, emit_wasm (WASM backend)
  │   └── cuda.rs      compile_cuda, eval_cuda (CUDA backend)
  ├── mir/mod.rs       WasmFunc, WasmInstr (intermediate representation)
  ├── main.rs          Demo: both WASM and CUDA paths
  └── lib.rs           Library exports

  tests/
  └── integration.rs   22 tests: unit + proptest (WASM 3-way + CUDA batch)

  proofs/
  └── Leanproof/
      ├── Basic.lean
      └── Correctness.lean   All theorems, 0 sorry, 0 axioms
```

## Verified Theorems

All proofs are in `proofs/Leanproof/Correctness.lean`. Zero sorry. Zero axioms.

| Theorem | What it proves |
|---|---|
| `compile_correct` | **Main theorem.** eval_js(e) = v implies exec(compile(e)) = [v] |
| `top_level_correct` | Corollary for closed programs |
| `eval_parallel_correct` | Batch = map of sequential (CUDA correctness) |
| `eval_parallel_nth` | Per-element independence (thread safety) |
| `eval_parallel_length` | Output length = input length |
| `eval_parallel_append` | Batch distributes over concatenation (block splitting) |
| `exec_append` | Exec distributes over instruction append |
| `compile_next_mono` | Compilation monotonically increases local counter |
| `acompile_correct` | Arithmetic fragment correctness |

## The Gap

The Lean proof verifies the **model**. The proptest suite validates the **implementation**. The correspondence between the Lean model and the Rust code is **not** formally verified. The trusted computing base includes: Lean's kernel, `rustc`, `wasmtime`, `wasm-encoder`.

## Quick Start

```bash
# Build and test Rust
cargo build && cargo test

# Build and verify Lean proofs
cd proofs && ~/.elan/bin/lake build
```

### Prerequisites

- Rust (edition 2024)
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) via elan (for proofs)
- Dependencies: `wasm-encoder`, `wasmtime` (dev), `proptest` (dev)

## License

MIT

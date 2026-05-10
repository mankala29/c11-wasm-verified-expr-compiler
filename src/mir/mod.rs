/// Stack-based WASM instructions — mirrors real WebAssembly.
#[derive(Debug, Clone, PartialEq)]
pub enum WasmInstr {
    I32Const(i32),
    I32Add,
    I32Sub,
    I32Mul,
    LocalGet(u32),
    LocalSet(u32),
}

/// A compiled WASM function: a sequence of instructions + how many locals it needs.
#[derive(Debug, Clone, PartialEq)]
pub struct WasmFunc {
    pub num_locals: u32,
    pub instrs: Vec<WasmInstr>,
}

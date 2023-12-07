pub use unicard_types::*;
use unicard_types_macro::WasmType32 as WasmType;

#[derive(WasmType)]
pub union Hello {
    one: i32,
    two: u32
}

fn main() {}
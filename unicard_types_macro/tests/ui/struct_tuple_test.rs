pub use unicard_types::*;
use unicard_types_macro::WasmType32 as WasmType;

#[derive(WasmType)]
struct ContainsInvalidTypes(std::fs::File);

fn main() {}
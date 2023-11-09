use unicard_types_macro::WasmType;

#[derive(WasmType)]
struct ContainsInvalidTypes(std::fs::File);

fn main() {}
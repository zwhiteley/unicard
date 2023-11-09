use unicard_types_macro::WasmType;

#[derive(WasmType)]
pub union Hello {
    one: i32,
    two: u32
}

fn main() {}
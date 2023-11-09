use unicard_types_macro::WasmType;

#[derive(WasmType)]
pub enum Test {
    A,
    B(*const i32),
    C {
        x: std::fs::File
    }
}

fn main() {}
use unicard_types_macro::WasmType;

#[derive(WasmType)]
pub enum Bar<'a, T> {
    Hello,
    World(&'a str),
    Cheese {
        x: T,
        y: T
    }
}

fn main() {}
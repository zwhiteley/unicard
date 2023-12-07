pub use unicard_types::*;
use unicard_types_macro::WasmType32 as WasmType;

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
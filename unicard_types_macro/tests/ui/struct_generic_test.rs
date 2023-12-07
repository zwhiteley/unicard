pub use unicard_types::*;
use unicard_types_macro::WasmType32 as WasmType;

#[derive(WasmType)]
pub struct Foo<'a> {
    my_str: &'a str
}

fn main() {}
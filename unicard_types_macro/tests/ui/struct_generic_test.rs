use unicard_types_macro::WasmType;

#[derive(WasmType)]
pub struct Foo<'a> {
    my_str: &'a str
}

fn main() {}
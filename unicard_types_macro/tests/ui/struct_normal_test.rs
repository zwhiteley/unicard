pub use unicard_types::*;
use unicard_types_macro::WasmType32 as WasmType;

#[derive(WasmType)]
struct Test {
    // NOTE: pointers will never be supported due to the lack of dereferencability
    // guarantees and an inability to pass them directly to WASM safely (except as
    // opaque types, although few languages support the use of such a feature).
    inner: *const i32
}

fn main() {}
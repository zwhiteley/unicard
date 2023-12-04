use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::spanned::Spanned;
use syn::{parse_macro_input, Data, DeriveInput};

mod shared;

mod struct_derive;

mod enum_derive;

#[proc_macro_derive(WasmType)]
pub fn wasm_type_macro(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(wasm_type(input))
}

fn wasm_type(input: DeriveInput) -> TokenStream {
    // There is little need for generic support, so don't implement it. This includes
    // support for lifetimes -- as `WasmType::read` allows for a value to be read,
    // it is impossible for any meaningful lifetime parameters to bee included
    if !input.generics.params.is_empty() {
        return quote_spanned!(
            input.generics.span() => ::std::compile_error!("WasmType does not support generics");
        );
    }

    // NOTE: as this is an internal macro, we do not need to support crate renaming
    match input.data {
        Data::Struct(data_struct) => struct_derive::derive(input.ident, data_struct),
        Data::Enum(data_enum) => enum_derive::derive(input.ident, data_enum),
        Data::Union(_) => {
            let span = proc_macro2::Span::call_site();
            quote_spanned!(span => ::std::compile_error!("the WasmType macro cannot be derived for unions");)
        }
    }
}

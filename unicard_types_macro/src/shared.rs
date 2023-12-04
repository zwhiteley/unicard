use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::{spanned::Spanned, FieldsNamed, FieldsUnnamed};

pub fn read_tuple_ctor(fields: &FieldsUnnamed) -> TokenStream {
    let init = fields.unnamed.iter().map(|field| {
        let ty = &field.ty;

        quote_spanned!(ty.span() =>
            <#ty as ::unicard_types::WasmType32>::read(&mut *reader)?
        )
    });

    quote!(#( #init ),*)
}

pub fn read_normal_ctor(fields: &FieldsNamed) -> TokenStream {
    let field_init = fields.named.iter().map(|field| {
        let name = field
            .ident
            .as_ref()
            .expect("fields on a named struct must be named");
        let ty = &field.ty;

        quote_spanned!(ty.span() =>
            #name: <#ty as ::unicard_types::WasmType32>::read(&mut *reader)?
        )
    });

    quote!( #( #field_init ),* )
}

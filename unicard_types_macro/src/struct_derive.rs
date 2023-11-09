use proc_macro2::{TokenStream, Ident};
use quote::{quote, quote_spanned};
use syn::{spanned::Spanned, DataStruct, Fields, FieldsNamed, FieldsUnnamed};

fn wasm_tuple_size(fields: &FieldsUnnamed) -> TokenStream {
    let size_part = fields
        .unnamed
        .iter()
        .enumerate()
        .map(|(idx, field)| {
            let idx = syn::Index::from(idx);
            let ty = &field.ty;

            quote_spanned!(ty.span() =>
                <#ty as ::unicard_types::WasmType>::size(&self.#idx)
            )
        });

    quote!(#( #size_part )+*)
}

fn wasm_tuple_write(fields: &FieldsUnnamed) -> TokenStream {
    let write_field = fields
        .unnamed
        .iter()
        .enumerate()
        .map(|(idx, field)| {
            let idx = syn::Index::from(idx);
            let ty = &field.ty;

            quote_spanned!(ty.span() =>
                <#ty as ::unicard_types::WasmType>::write(&self.#idx, &mut *writer)?;
            )
        });

    quote!(#( #write_field )*)
}


fn wasm_normal_size(fields: &FieldsNamed) -> TokenStream {
    let size_part = fields
        .named
        .iter()
        .map(|field| {
            let ident = field.ident.as_ref().expect("named structs should have named fields");
            let ty = &field.ty;

            quote_spanned!(ty.span() =>
                <#ty as ::unicard_types::WasmType>::size(&self.#ident)
            )
        });

    quote!(#( #size_part )+*)
}

fn wasm_normal_write(fields: &FieldsNamed) -> TokenStream {
    let write_stmt = fields
        .named
        .iter()
        .map(|field| {
            let ident = field
                .ident
                .as_ref()
                .expect("named struct to have named fields");

            let ty = &field.ty;

            quote_spanned!(ty.span() =>
                <#ty as ::unicard_types::WasmType>::write(&self.#ident, &mut *writer)?;
            )
        });

    quote!( #( #write_stmt )* )
}

pub fn derive(struct_ident: Ident, data_struct: DataStruct) -> TokenStream {
    match data_struct.fields {
        Fields::Unit => {
            quote!(
                #[automatically_derived]
                impl ::unicard_types::WasmType for #struct_ident where Self: ::std::marker::Sized {
                    fn read(_reader: &mut impl ::unicard_types::WasmReader) -> ::core::result::Result<Self, ::unicard_types::WasmMemoryError> {
                        ::core::result::Result::Ok(Self)
                    }

                    fn size(&self) -> usize {
                        0usize
                    }

                    fn write(&self, _writer: &mut impl ::unicard_types::WasmWriter) -> ::core::result::Result<(), ::unicard_types::WasmMemoryError> {
                        ::core::result::Result::Ok(())
                    }
                }
            )
        }
        Fields::Unnamed(unnamed_fields) => {
            let constructor = crate::shared::read_tuple_ctor(&unnamed_fields);
            let size_body = wasm_tuple_size(&unnamed_fields);
            let write_fields = wasm_tuple_write(&unnamed_fields);

            quote!(
                #[automatically_derived]
                impl ::unicard_types::WasmType for #struct_ident where Self: ::std::marker::Sized {
                    fn read(reader: &mut impl ::unicard_types::WasmReader) -> ::core::result::Result<Self, ::unicard_types::WasmMemoryError> {
                        ::core::result::Result::Ok(Self( #constructor ))
                    }

                    fn size(&self) -> usize {
                        #size_body
                    }

                    fn write(&self, writer: &mut impl ::unicard_types::WasmWriter) -> ::core::result::Result<(), ::unicard_types::WasmMemoryError> {
                        #write_fields
                        ::core::result::Result::Ok(())
                    }
                }
            )
        }
        Fields::Named(named_fields) => {
            let constructor = crate::shared::read_normal_ctor(&named_fields);
            let size_body = wasm_normal_size(&named_fields);
            let write_body = wasm_normal_write(&named_fields);

            quote!(
                #[automatically_derived]
                impl ::unicard_types::WasmType for #struct_ident where Self: ::std::marker::Sized {
                    fn read(reader: &mut impl ::unicard_types::WasmReader) -> ::core::result::Result<Self, ::unicard_types::WasmMemoryError> {
                        ::core::result::Result::Ok(Self { #constructor })
                    }

                    fn size(&self) -> usize {
                        #size_body
                    }

                    fn write(&self, writer: &mut impl ::unicard_types::WasmWriter) -> ::core::result::Result<(), ::unicard_types::WasmMemoryError> {
                        #write_body
                        Ok(())
                    }
                }
            )
        }
    }
}

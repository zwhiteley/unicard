use proc_macro2::{Ident, TokenStream};
use quote::{quote, quote_spanned};
use syn::{spanned::Spanned, DataStruct, Fields, FieldsNamed, FieldsUnnamed};

fn wasm_tuple_size(fields: &FieldsUnnamed) -> TokenStream {
    let size_part = fields.unnamed.iter().enumerate().map(|(idx, field)| {
        let idx = syn::Index::from(idx);
        let ty = &field.ty;

        quote_spanned!(ty.span() =>
            .checked_add(<#ty as crate::WasmType32>::size(&self.#idx)?)?
        )
    });

    quote!(0u32 #( #size_part )*)
}

fn wasm_tuple_write(fields: &FieldsUnnamed) -> TokenStream {
    let write_field = fields.unnamed.iter().enumerate().map(|(idx, field)| {
        let idx = syn::Index::from(idx);
        let ty = &field.ty;

        quote_spanned!(ty.span() =>
            <#ty as crate::WasmType32>::write(&self.#idx, &mut *writer)?;
        )
    });

    quote!(#( #write_field )*)
}

fn wasm_normal_size(fields: &FieldsNamed) -> TokenStream {
    let size_part = fields.named.iter().map(|field| {
        let ident = field
            .ident
            .as_ref()
            .expect("named structs should have named fields");
        let ty = &field.ty;

        quote_spanned!(ty.span() =>
            .checked_add(<#ty as crate::WasmType32>::size(&self.#ident)?)?
        )
    });

    quote!(0u32 #( #size_part )*)
}

fn wasm_normal_write(fields: &FieldsNamed) -> TokenStream {
    let write_stmt = fields.named.iter().map(|field| {
        let ident = field
            .ident
            .as_ref()
            .expect("named struct to have named fields");

        let ty = &field.ty;

        quote_spanned!(ty.span() =>
            <#ty as crate::WasmType32>::write(&self.#ident, &mut *writer)?;
        )
    });

    quote!( #( #write_stmt )* )
}

pub fn derive(struct_ident: Ident, data_struct: DataStruct) -> TokenStream {
    match data_struct.fields {
        Fields::Unit => {
            quote!(
                #[automatically_derived]
                impl crate::WasmType32 for #struct_ident where Self: ::std::marker::Sized {
                    fn read(_reader: &mut impl crate::WasmReader32) -> ::core::result::Result<Self, crate::WasmMemoryError32> {
                        ::core::result::Result::Ok(Self)
                    }

                    fn size(&self) -> Option<u32> {
                        Some(0u32)
                    }

                    fn write(&self, _writer: &mut impl crate::WasmWriter32) -> ::core::result::Result<(), crate::WasmMemoryError32> {
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
                impl crate::WasmType32 for #struct_ident where Self: ::std::marker::Sized {
                    fn read(reader: &mut impl crate::WasmReader32) -> ::core::result::Result<Self, crate::WasmMemoryError32> {
                        ::core::result::Result::Ok(Self( #constructor ))
                    }

                    fn size(&self) -> Option<u32> {
                        Some(#size_body)
                    }

                    fn write(&self, writer: &mut impl crate::WasmWriter32) -> ::core::result::Result<(), crate::WasmMemoryError32> {
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
                impl crate::WasmType32 for #struct_ident where Self: ::std::marker::Sized {
                    fn read(reader: &mut impl crate::WasmReader32) -> ::core::result::Result<Self, crate::WasmMemoryError32> {
                        ::core::result::Result::Ok(Self { #constructor })
                    }

                    fn size(&self) -> Option<u32> {
                        Some(#size_body)
                    }

                    fn write(&self, writer: &mut impl crate::WasmWriter32) -> ::core::result::Result<(), crate::WasmMemoryError32> {
                        #write_body
                        Ok(())
                    }
                }
            )
        }
    }
}

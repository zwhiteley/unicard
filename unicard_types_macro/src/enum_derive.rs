use proc_macro2::{TokenStream, Ident};
use quote::{format_ident, quote, quote_spanned};
use syn::{spanned::Spanned, DataEnum, Fields, Field};

/// Convert a variant of an enum to a branch of a match statement.
///
/// This trait is required as closures do not support generics (if they did,
/// we'd just use the [`branchify`] function with a closure rather than use
/// a trait).
///
/// The purpose of this trait is to simplify enum code generation: rather than have 3 separate
/// implementations converting the three different variant types (unit, tuple, and named) into
/// match bodies, this trait can be used instead to apply the same implementation to all three
/// types (as most implementations don't care about the type of the variant, only unwrapping
/// the fields it contains).
trait Branchify {
    /// Convert a variant of an enum to the body of a match expression, given the
    /// variant's assigned discriminant and an iterator over all the variant's fields.
    ///
    /// # Example
    ///
    /// Consider the following code:
    ///
    /// ```
    /// enum Foo {
    ///     Bar,
    ///     Baz(u8),
    ///     FooBar {
    ///         inner: u32
    ///     }
    /// }
    ///
    /// # /*
    /// fn main() {
    ///     let foo = ...;
    ///     match foo {
    ///         Foo::Bar => BODY_BAR,
    ///         Foo::Baz(field0) => BODY_BAZ,
    ///         Foo::Bar {
    ///             inner: field0
    ///         } => BODY_FOOBAR,
    ///     }
    /// }
    /// # */
    /// ```
    ///
    /// The same branchify implementation will be called three times (with the corresponding
    /// arguments) to generate the code for `BODY_BAR`, `BODY_BAZ`, and `BODY_FOOBAR` respectively.
    ///
    /// # Remarks
    ///
    /// An empty iterator may be passed (e.g., in the case of a unit variant, empty tuple variant,
    /// etc).
    fn branchify<'a>(&mut self, discriminator: u32, iterator: impl Iterator<Item=(Ident, &'a Field)>) -> TokenStream;
}

/// Create a body of a match statement from a the definition of an enum.
///
/// `branchifier` specifies how each variant should be converted to a match arm expression (see
/// [`Branchify`] for more information).
///
/// # Example
///
/// ```
/// enum Foo {
///     Bar,
///     Baz(u8),
///     FooBar {
///         inner: u32
///     }
/// }
///
/// # /*
/// fn main() {
///     let foo: Foo = ...;
///     match foo {
///         #BRANCHIFY_RESULT
///     }
/// }
/// # */
/// ```
///
/// `#BRANCHIFY_RESULT` is the result of a `branchify` call with `Foo`'s data and a branchifier
/// to convert each enum into an expression.
fn branchify(data_enum: &DataEnum, mut branchifier: impl Branchify) -> TokenStream {
    let branches = data_enum
        .variants
        .iter()
        .enumerate()
        .map(|(idx, variant)| {
            // NOTE: we have already checked to ensure the variant count is <= u32::MAX,
            // so this is fine
            let discriminator = idx as u32;
            let var_ident = &variant.ident;

            match &variant.fields {
                Fields::Unit => {
                    // A unit variant has no fields, so pass an empty iterator
                    let body = branchifier.branchify(discriminator, std::iter::empty());
                    quote!(Self::#var_ident => { #body })
                }
                Fields::Unnamed(fields) => {
                    // Create the variable idents to be used for each of the tuple fields
                    // (e.g., `__field0` for `variant.0`)
                    let field_iter = fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(idx, field)| (
                            format_ident!("__field{idx}"),
                            field
                        ));

                    // Generate the match arm pattern (to bind the tuple parts to variable names
                    // e.g., `Foo::Baz(__field0, __field1)`)
                    let pattern = {
                        let idents = field_iter.clone()
                            .map(|(ident, _)| ident);

                        quote!(Self::#var_ident( #( #idents ),* ))
                    };

                    // Use `branchifier` to generate the expression of the match arm
                    let body = branchifier.branchify(discriminator, field_iter);

                    quote!(#pattern => { #body })
                }
                Fields::Named(fields) => {
                    // Create the variable idents to be used for each of the tuple fields
                    // (e.g., `__field0` for `variant.inner`)
                    let field_iter = fields
                        .named
                        .iter()
                        .enumerate()
                        .map(|(idx, field)| (
                            format_ident!("__field{idx}"),
                            field
                        ));

                    // Generate the match arm pattern which binds to the identifiers created
                    // above (e.g., `Foo::FooBar { inner: __field0 }`).
                    let pattern = {
                        let idents = field_iter.clone()
                            .map(|(ident, field)| {
                                let field_ident = &field.ident;
                                quote!(#field_ident: #ident)
                            });

                        quote!(Self::#var_ident { #( #idents ),* })
                    };

                    // Use `branchifier` to generate the match express body
                    let body = branchifier.branchify(discriminator, field_iter);

                    quote!(#pattern => { #body })
                }
            }
        });

    // Aggregate the match arms into a match body
    quote!(#( #branches ),*)
}

/// Derive `WasmType` for an enum.
pub fn derive(enum_ident: Ident, data_enum: DataEnum) -> TokenStream {
    // we encode the discriminant as a u32, meaning there cannot be more than
    // u32 variants.
    // NOTE: This check isn't strictly necessary: any enum with u32::MAX variants
    //       is bound to cause performance issues (not to mention the file will
    //       be at least 4GiB in size). Furthermore, I believe the rust compiler
    //       is capped at i32::MAX bytes, meaning a rust project with more than
    //       2GiB of files (e.g., from an enum with u32::MAX variants) won't
    //       compile anyway. We keep this check here just in case any of the above
    //       change.
    if data_enum.variants.len() > (u32::MAX as usize) {
        let error_msg = format!("enum cannot have more than {} variants", u32::MAX);
        return quote_spanned!(enum_ident.span() => ::std::compile_error!(#error_msg););
    }

    let read_body = {
        let branches = data_enum
            .variants
            .iter()
            .enumerate()
            .map(|(discriminator, variant)| {
                let discriminator = discriminator as u32;
                let ident = &variant.ident;

                match &variant.fields {
                    Fields::Unit => quote!(#discriminator => Self::#ident),
                    Fields::Unnamed(unnamed) => {
                        let ctor = crate::shared::read_tuple_ctor(unnamed);
                        quote!(#discriminator => Self::#ident(#ctor))
                    }
                    Fields::Named(named) => {
                        let ctor = crate::shared::read_normal_ctor(named);
                        quote!(#discriminator => Self::#ident { #ctor })
                    }
                }
            });

        quote!(
            let discriminator = <u32 as ::unicard_types::WasmType>::read(&mut *reader)?;

            ::core::result::Result::Ok(match discriminator {
                #(
                    #branches
                ),*,
                _ => return ::core::result::Result::Err(::unicard_types::WasmMemoryError::invalid_value())
            })
        )
    };

    let size_body = {
        struct SizeBranchify;

        impl Branchify for SizeBranchify {
            fn branchify<'a>(&mut self, discriminator: u32, iterator: impl Iterator<Item=(Ident, &'a Field)>) -> TokenStream {
                let u32_size = quote!(<u32 as ::unicard_types::WasmType>::size(&#discriminator));
                let sizes = iterator.map(|(ident, field)| {
                    let ty = &field.ty;
                    quote_spanned!(ty.span() =>
                        <#ty as ::unicard_types::WasmType>::size(&#ident)
                    )
                });

                quote!(#u32_size #(+ #sizes)*)
            }
        }

        let branches = branchify(&data_enum, SizeBranchify);
        quote!(
            match self {
                #branches
            }
        )
    };

    let write_body = {
        struct WriteBranchify;

        impl Branchify for WriteBranchify {
            fn branchify<'a>(&mut self, discriminator: u32, iterator: impl Iterator<Item=(Ident, &'a Field)>) -> TokenStream {
                let write_u32 = quote!(<u32 as ::unicard_types::WasmType>::write(&#discriminator, &mut *writer)?);
                let write_stmts = iterator.map(|(ident, field)| {
                    let ty = &field.ty;
                    quote_spanned!(ty.span() =>
                        <#ty as ::unicard_types::WasmType>::write(&#ident, &mut *writer)?
                    )
                });

                quote!(#write_u32; #( #write_stmts; )*)
            }
        }

        let branches = branchify(&data_enum, WriteBranchify);
        quote!(
            match self {
                #branches
            }
        )
    };

    quote!(
        #[automatically_derived]
        impl ::unicard_types::WasmType for #enum_ident where Self: ::std::marker::Sized {
            fn read(reader: &mut impl ::unicard_types::WasmReader) -> ::core::result::Result<Self, ::unicard_types::WasmMemoryError> {
                #read_body
            }

            fn size(&self) -> usize {
                #size_body
            }

            fn write(&self, writer: &mut impl ::unicard_types::WasmWriter) -> ::core::result::Result<(), ::unicard_types::WasmMemoryError> {
                #write_body
                ::core::result::Result::Ok(())
            }
        }
    )
}


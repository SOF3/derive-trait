//! Derive a trait and a delegating impl from an inherent impl block.
//!
//! # Why go the opposite way?
//! This macro is designated for single generic types with many small impl blocks
//! and complex type bounds in each impl block.
//!
//! - Without a trait, the function user needs to repeat all the type bounds in the impl block
//!   in every function that requests a type supporting the associated functions.
//! - Without a macro, the function author needs to write each function signature four times
//!   (the trait, the inherent impl, the trait impl and delegation)
//!   and the type bounds twice.
//! - With the `#[inherent]` macro, the function author would still need to write twice
//!  (the trait and the trait impl).
//!
//! Note that use of thsi crate is only advisable for impl blocks with complicated type bounds.
//! It is not advisable to create single-implementor traits blindly.

use heck::ToPascalCase;
use itertools::Itertools;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_quote, parse_quote_spanned, Error, Result};

#[proc_macro_attribute]
pub fn derive_trait(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    real_derive_trait(attr.into(), item.into()).unwrap_or_else(Error::into_compile_error).into()
}

fn real_derive_trait(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let attr: Attr = syn::parse2(attr)?;
    let Attr { debug_print, vis, trait_ident, supers, generics: trait_generics } = &attr;
    let debug_print = debug_print.is_some();
    let (_, trait_generics_ref, _) = trait_generics.split_for_impl();

    let inherent_impl: syn::ItemImpl = syn::parse2(item)?;

    let mut trait_item = syn::ItemTrait {
        attrs:       Vec::new(),
        vis:         vis.clone(),
        unsafety:    None,
        auto_token:  None,
        restriction: None,
        trait_token: syn::Token![trait](Span::call_site()),
        ident:       trait_ident.clone(),
        generics:    trait_generics.clone(),
        colon_token: supers.as_ref().map(|&(colon, _)| colon),
        supertraits: supers.clone().map(|(_, supers)| supers).unwrap_or_default(),
        brace_token: syn::token::Brace(Span::call_site()),
        items:       Vec::new(),
    };

    let mut trait_impl_item = syn::ItemImpl {
        attrs:       Vec::new(),
        unsafety:    None,
        defaultness: None,
        impl_token:  syn::Token![impl](Span::call_site()),
        generics:    inherent_impl.generics.clone(),
        trait_:      Some((
            None,
            syn::parse_quote!(#trait_ident #trait_generics_ref),
            syn::Token![for](Span::call_site()),
        )),
        self_ty:     inherent_impl.self_ty.clone(),
        brace_token: syn::token::Brace(Span::call_site()),
        items:       Vec::new(),
    };

    let self_ty = &*inherent_impl.self_ty;

    for item in &inherent_impl.items {
        match item {
            syn::ImplItem::Fn(item) => {
                let mut sig = item.sig.clone();
                let sig_span = sig.span();

                if let syn::ReturnType::Type(r_arrow, ret_ty) = &sig.output {
                    let transformed = for_each_impl_trait(ret_ty, &mut |tit| {
                        let span = tit.span();

                        // convert return-position-impl-trait into associated-type-impl-trait
                        let assoc_ident = item.sig.ident.to_string().to_pascal_case();
                        let assoc_ident = syn::Ident::new(&assoc_ident, span);
                        let ty_bounds = &tit.bounds;

                        // for now, assume all generic parameters are required.
                        // we cannot infer whether the signature involves an implicit lifetime,
                        // so for simplicity we require all implicit lifetimes to be explicitly
                        // documented for now.

                        let (assoc_generics, assoc_generics_names, assoc_where) = if sig
                            .generics
                            .params
                            .is_empty()
                        {
                            (None, None, None)
                        } else {
                            let (sig_impl_generics, sig_ty_generics, sig_where_generics) =
                                sig.generics.split_for_impl();
                            let mut sig_impl_generics: syn::Generics =
                                syn::parse_quote!(#sig_impl_generics);
                            let mut sig_ty_generics: syn::AngleBracketedGenericArguments =
                                syn::parse_quote!(#sig_ty_generics);
                            let mut sig_where_generics = sig_where_generics.cloned();

                            if let Some(recv) = sig.receiver() {
                                if let Some((and, lt)) = &recv.reference {
                                    let lt = match lt {
                                        Some(lt) => lt.clone(),
                                        None => {
                                            let lt: syn::Lifetime =
                                                syn::parse_quote_spanned!(and.span() => '__self);
                                            sig_impl_generics.params.push(
                                                syn::GenericParam::Lifetime(parse_quote!(#lt)),
                                            );
                                            sig_ty_generics
                                                .args
                                                .push(syn::parse_quote_spanned!(and.span() => '_));
                                            lt
                                        }
                                    };
                                    let where_predicate: syn::WherePredicate =
                                        syn::parse_quote_spanned!(and.span() => Self: #lt);
                                    sig_where_generics.get_or_insert(syn::WhereClause {
                                        where_token: syn::Token![where](sig_span),
                                        predicates: Punctuated::new(),
                                    }).predicates.push(syn::parse_quote_spanned!(and.span() => #where_predicate));
                                }
                            }

                            (
                                Some(quote!(#sig_impl_generics)),
                                Some(quote!(#sig_ty_generics)),
                                Some(quote!(#sig_where_generics)),
                            )
                        };

                        let assoc_doc = format!(
                            "Return value for [`{fn_ident}`](Self::{fn_ident})",
                            fn_ident = &sig.ident
                        );
                        trait_item.items.push(parse_quote_spanned! { span =>
                            #[doc = #assoc_doc]
                            type #assoc_ident #assoc_generics: #ty_bounds #assoc_where;
                        });
                        trait_impl_item.items.push(parse_quote_spanned! { span =>
                            type #assoc_ident #assoc_generics = #tit #assoc_where;
                        });

                        parse_quote_spanned! { span =>
                            Self::#assoc_ident #assoc_generics_names
                        }
                    });
                    sig.output = syn::ReturnType::Type(*r_arrow, Box::new(transformed));
                }

                let sig_ident = &sig.ident;
                let sig_args: Vec<syn::Pat> = sig
                    .inputs
                    .iter()
                    .map(|input| match input {
                        syn::FnArg::Receiver(syn::Receiver { self_token, .. }) => {
                            parse_quote!(#self_token)
                        }
                        syn::FnArg::Typed(typed) => (*typed.pat).clone(),
                    })
                    .collect();

                let fn_docs: Vec<_> =
                    item.attrs.iter().filter(|attr| attr.path().is_ident("doc")).cloned().collect();

                trait_item.items.push(syn::TraitItem::Fn(syn::TraitItemFn {
                    attrs:      fn_docs.clone(),
                    sig:        sig.clone(),
                    default:    None,
                    semi_token: Some(syn::Token![;](item.span())),
                }));
                trait_impl_item.items.push(syn::ImplItem::Fn(syn::ImplItemFn {
                    attrs:       fn_docs.clone(),
                    vis:         syn::Visibility::Inherited,
                    defaultness: None,
                    sig:         sig.clone(),
                    block:       parse_quote_spanned! { item.span() => {
                        <#self_ty>::#sig_ident(#(#sig_args),*)
                    }},
                }));
            }
            _ => return Err(Error::new_spanned(item, "only associated functions are supported")),
        }
    }

    let trait_item_doc = format!(
        "Derived trait for [`{}`].",
        match self_ty {
            syn::Type::Path(path) =>
                path.path.segments.iter().map(|ident| ident.ident.to_string()).join("::"),
            _ => quote!(#self_ty).to_string(),
        }
    );

    let output = quote! {
        #[allow(clippy::needless_lifetimes)]
        #inherent_impl
        #[allow(clippy::needless_lifetimes, non_camel_case_types)]
        #[doc = #trait_item_doc]
        #trait_item
        #[automatically_derived]
        #[allow(clippy::needless_lifetimes, non_camel_case_types)]
        #trait_impl_item
    };
    if debug_print {
        println!("{}", output);
    }
    Ok(output)
}

fn for_each_impl_trait(
    ty: &syn::Type,
    f: &mut impl FnMut(&syn::TypeImplTrait) -> syn::Type,
) -> syn::Type {
    match ty {
        syn::Type::Array(ty) => syn::Type::Array(syn::TypeArray {
            elem: Box::new(for_each_impl_trait(&*ty.elem, f)),
            ..ty.clone()
        }),
        syn::Type::BareFn(ty) => syn::Type::BareFn(syn::TypeBareFn {
            inputs: ty
                .inputs
                .clone()
                .into_pairs()
                .map(|mut pair| {
                    let value = pair.value_mut();
                    value.ty = for_each_impl_trait(&value.ty, f);
                    pair
                })
                .collect(),
            ..ty.clone()
        }),
        syn::Type::Group(_) => ty.clone(),
        syn::Type::ImplTrait(ty) => f(ty),
        syn::Type::Infer(_) => ty.clone(),
        syn::Type::Macro(_) => ty.clone(),
        syn::Type::Never(_) => ty.clone(),
        syn::Type::Paren(ty) => syn::Type::Paren(syn::TypeParen {
            elem: Box::new(for_each_impl_trait(&*ty.elem, f)),
            ..ty.clone()
        }),
        syn::Type::Path(ty) => syn::Type::Path(syn::TypePath {
            qself: ty.qself.clone().map(|mut qself| {
                qself.ty = Box::new(for_each_impl_trait(&*qself.ty, f));
                qself
            }),
            path:  for_each_impl_trait_in_path(&ty.path, f),
        }),
        syn::Type::Ptr(ty) => syn::Type::Ptr(syn::TypePtr {
            elem: Box::new(for_each_impl_trait(&*ty.elem, f)),
            ..ty.clone()
        }),
        syn::Type::Reference(ty) => syn::Type::Reference(syn::TypeReference {
            elem: Box::new(for_each_impl_trait(&*ty.elem, f)),
            ..ty.clone()
        }),
        syn::Type::Slice(ty) => syn::Type::Slice(syn::TypeSlice {
            elem: Box::new(for_each_impl_trait(&*ty.elem, f)),
            ..ty.clone()
        }),
        syn::Type::TraitObject(ty) => syn::Type::TraitObject(syn::TypeTraitObject {
            bounds: ty
                .bounds
                .clone()
                .into_pairs()
                .map(|mut pair| {
                    if let syn::TypeParamBound::Trait(bound) = pair.value_mut() {
                        bound.path = for_each_impl_trait_in_path(&bound.path, f);
                    }
                    pair
                })
                .collect(),
            ..ty.clone()
        }),
        syn::Type::Tuple(ty) => syn::Type::Tuple(syn::TypeTuple {
            elems: ty
                .elems
                .clone()
                .into_pairs()
                .map(|mut pair| {
                    let value = pair.value_mut();
                    *value = for_each_impl_trait(&value, f);
                    pair
                })
                .collect(),
            ..ty.clone()
        }),
        syn::Type::Verbatim(_) => ty.clone(),
        _ => ty.clone(),
    }
}

fn for_each_impl_trait_in_path(
    path: &syn::Path,
    f: &mut impl FnMut(&syn::TypeImplTrait) -> syn::Type,
) -> syn::Path {
    syn::Path {
        leading_colon: path.leading_colon,
        segments:      path
            .segments
            .clone()
            .into_pairs()
            .map(|mut pair| {
                let value = pair.value_mut();
                match &mut value.arguments {
                    syn::PathArguments::None => {}
                    syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                        args,
                        ..
                    }) => {
                        for pair in args.pairs_mut() {
                            match pair.into_value() {
                                syn::GenericArgument::Type(ty) => *ty = for_each_impl_trait(ty, f),
                                syn::GenericArgument::AssocType(ty) => {
                                    ty.ty = for_each_impl_trait(&ty.ty, f)
                                }
                                _ => {}
                            }
                        }
                    }
                    syn::PathArguments::Parenthesized(syn::ParenthesizedGenericArguments {
                        inputs,
                        output,
                        ..
                    }) => {
                        for input in inputs {
                            *input = for_each_impl_trait(input, f);
                        }
                        if let syn::ReturnType::Type(_, ty) = output {
                            *ty = Box::new(for_each_impl_trait(ty, f));
                        }
                    }
                }
                pair
            })
            .collect(),
    }
}

struct Attr {
    debug_print: Option<kw::__debug_print>,
    vis:         syn::Visibility,
    trait_ident: syn::Ident,
    generics:    syn::Generics,
    supers:      Option<(syn::Token![:], Punctuated<syn::TypeParamBound, syn::Token![+]>)>,
}

impl Parse for Attr {
    fn parse(input: ParseStream) -> Result<Self> {
        let debug_print = input.parse::<kw::__debug_print>().ok();
        let vis = input.parse()?;
        let trait_ident = input.parse()?;
        let mut generics = syn::Generics::default();
        let mut supers = None;

        while !input.is_empty() {
            let lh = input.lookahead1();
            if generics.lt_token.is_none() && lh.peek(syn::Token![<]) {
                generics = input.parse()?;
            } else if lh.peek(syn::Token![:]) {
                supers = Some((input.parse()?, Punctuated::parse_separated_nonempty(input)?));
            } else if !generics.params.is_empty() && lh.peek(syn::Token![where]) {
                generics.where_clause = Some(input.parse()?);
            } else {
                return Err(lh.error());
            }
        }

        Ok(Self { debug_print, vis, trait_ident, supers, generics })
    }
}

mod kw {
    use syn::custom_keyword;

    custom_keyword!(Sized);
    custom_keyword!(__debug_print);
}

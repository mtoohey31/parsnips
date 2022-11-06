// #![no_std]
#![deny(clippy::alloc_instead_of_core)]
#![deny(clippy::allow_attributes_without_reason)]
// TODO: enable this when clippy hits 1.66.0
// #![deny(clippy::as_ptr_cast_mut)]
#![deny(clippy::cast_possible_truncation)]
#![deny(clippy::dbg_macro)]
#![deny(clippy::equatable_if_let)]
#![deny(clippy::filter_map_next)]
#![deny(clippy::flat_map_option)]
#![deny(clippy::map_unwrap_or)]
#![deny(clippy::missing_panics_doc)]
#![deny(clippy::option_if_let_else)]
#![deny(clippy::panic)]
#![deny(clippy::std_instead_of_alloc)]
#![deny(clippy::std_instead_of_core)]
#![deny(clippy::todo)]
#![deny(clippy::wildcard_enum_match_arm)]
#![deny(clippy::wildcard_imports)]
#![deny(macro_use_extern_crate)]
// TODO: enable this when things are stable
// #![deny(missing_docs)]
#![deny(unused_crate_dependencies)]
#![deny(unused_extern_crates)]
#![deny(unused_lifetimes)]
#![deny(unused_qualifications)]

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, TokenStream, TokenTree};

#[proc_macro]
#[allow(clippy::panic)]
/// # Panics
///
/// This macro panics (at compile time) when given invalid input. Valid input is of the form:
///
/// IDENTIFIER `:` (, IDENTIFIER)* `,`?
pub fn encoding_table(tokens: TokenStream) -> TokenStream {
    // the full result
    let mut res = TokenStream::new();
    // the stream for enum members, which is added as a group at the end
    let mut members = TokenStream::new();

    let mut ti = tokens.into_iter().enumerate();

    let enum_ident = match ti.next() {
        Some((_, TokenTree::Ident(i))) => {
            match ti.next() {
                Some((_, TokenTree::Punct(p))) if p.as_char() == ':' => {}
                None => {}
                Some((_, t)) => panic!("unexpected token '{}', expected ':'", t),
            }
            i
        }
        Some((_, t)) => panic!("unexpected token '{}', expected enum name identifier", t),
        None => panic!("expected enum name identifier"),
    };

    while let Some((n, TokenTree::Ident(i))) = ti.next() {
        // "_" is used to indicate reserved instructions
        if i.to_string() != "_" {
            let span = i.span();
            let val: u8 = ((n - 2) / 2)
                .try_into()
                .expect("encoding table contains too many items to fit within a byte");
            res.extend([
                TokenTree::Ident(Ident::new("pub", span)),
                TokenTree::Ident(Ident::new("const", span)),
                TokenTree::Ident(i.clone()),
                TokenTree::Punct(Punct::new(':', Spacing::Alone)),
                TokenTree::Ident(Ident::new("u8", span)),
                TokenTree::Punct(Punct::new('=', Spacing::Alone)),
                TokenTree::Literal(Literal::u8_unsuffixed(val)),
                TokenTree::Punct(Punct::new(';', Spacing::Alone)),
            ]);
            members.extend([
                TokenTree::Ident(i),
                TokenTree::Punct(Punct::new('=', Spacing::Alone)),
                TokenTree::Literal(Literal::u8_unsuffixed(val)),
                TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            ]);
        }
        match ti.next() {
            Some((_, TokenTree::Punct(p))) if p.as_char() == ',' => {}
            Some((_, t)) => panic!("unexpected token '{}', expected ',' or EOF", t),
            None => break,
        }
    }
    if let Some((_, t)) = ti.next() {
        panic!("unexpected token '{}', expected identifier or EOF", t);
    }

    res.extend("#[repr(u8)]".parse::<TokenStream>());
    res.extend("pub enum".parse::<TokenStream>());
    res.extend([
        TokenTree::Ident(enum_ident),
        TokenTree::Group(Group::new(Delimiter::Brace, members)),
    ]);

    res
}

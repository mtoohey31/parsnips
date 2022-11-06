#![deny(
    clippy::alloc_instead_of_core,
    clippy::allow_attributes_without_reason,
    // TODO: enable this when clippy hits 1.66.0
    // clippy::as_ptr_cast_mut,
    clippy::cast_possible_truncation,
    clippy::dbg_macro,
    clippy::equatable_if_let,
    clippy::filter_map_next,
    clippy::flat_map_option,
    clippy::map_unwrap_or,
    clippy::missing_panics_doc,
    clippy::option_if_let_else,
    clippy::panic,
    clippy::std_instead_of_alloc,
    clippy::std_instead_of_core,
    clippy::todo,
    clippy::wildcard_enum_match_arm,
    clippy::wildcard_imports,
    macro_use_extern_crate,
    // TODO: enable this when things are stable
    // missing_docs,
    unused_crate_dependencies,
    unused_extern_crates,
    unused_lifetimes,
    unused_qualifications,
)]

use proc_macro::{Delimiter, Group, Literal, Punct, Spacing, TokenStream, TokenTree};

/// Populates enum variants using an encoding table provided to the attribute macro. Syntax:
///
/// IDENTIFIER (, IDENTIFIER)* `,`?
///
/// # Panics
///
/// This macro panics (at compile time) when given invalid input.
#[proc_macro_attribute]
#[allow(clippy::panic)]
pub fn from_encoding_table(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item_vec = item.into_iter().collect::<Vec<_>>();
    match item_vec.pop() {
        Some(TokenTree::Group(g)) if g.stream().is_empty() => {}
        Some(t) => panic!(
            "unexpected ending token for enum declaration '{}'; expected '{{}}'",
            t
        ),
        None => panic!("no ending token for enum declaration"),
    }

    let mut enum_members = TokenStream::new();

    let mut ti = attr.into_iter().enumerate();
    while let Some((n, TokenTree::Ident(i))) = ti.next() {
        // "_" is used to indicate reserved instructions
        if i.to_string() != "_" {
            enum_members.extend([
                TokenTree::Ident(i),
                TokenTree::Punct(Punct::new('=', Spacing::Alone)),
                TokenTree::Literal(Literal::usize_unsuffixed(n / 2)),
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

    item_vec.push(TokenTree::Group(Group::new(Delimiter::Brace, enum_members)));
    TokenStream::from_iter(item_vec)
}

#![no_std]

#[cfg(test)]
#[macro_use]
extern crate alloc;

mod lex;
mod parse;

pub use parse::parse;
pub use parse::Ast;

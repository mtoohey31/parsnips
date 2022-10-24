// TODO: uncommment this when https://github.com/rust-lang/rust/issues/48665
// gets fixed some day, or if there's a better workaround
// #![no_std]

pub mod inst;
pub use inst::{Funct, Inst, Op};

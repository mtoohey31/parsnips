#[macro_use]
extern crate pest_derive;

#[derive(Parser)]
#[grammar = "mips.pest"]
pub struct MIPSParser;

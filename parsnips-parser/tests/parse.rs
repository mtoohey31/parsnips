use parsnips_parser::{MIPSParser, Rule};
use pest::Parser;

#[test]
fn test_fibonacci() {
    dbg!(MIPSParser::parse(
        Rule::file,
        include_str!("./Fibonacci.asm")
    ));
}

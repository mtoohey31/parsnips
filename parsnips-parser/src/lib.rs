#![no_std]

mod lex;
use core::num::IntErrorKind;

use lex::{lex, LexError, TokenKind};

extern crate alloc;
use alloc::vec::Vec;
use strum_macros::EnumString;

#[derive(Debug, PartialEq, Eq)]
pub struct Ast<'a> {
    pub sections: Vec<Section<'a>>,
}

impl Ast<'_> {
    fn new() -> Self {
        Self {
            sections: Vec::new(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Section<'a> {
    Data(Vec<Data<'a>>),
    Text(Vec<Entry<'a>>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Entry<'a> {
    Label(&'a str),
    Instruction(Instruction<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Instruction<'a> {
    pub name: &'a str,
    pub arguments: Vec<Argument<'a>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Argument<'a> {
    Register(&'a str),
    OffsetRegister {
        offset: NumLiteral<'a>,
        register: &'a str,
    },
    Literal(Literal<'a>),
    Label(&'a str),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal<'a> {
    Num(NumLiteral<'a>),
    Char(char),
    Str(&'a str),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NumLiteral<'a> {
    // this is a field because we can't take a slice of the input that
    // includes just the sign and the number body when there's a 0b, 0o, 0x
    // prefix
    pub negative: bool,
    pub radix: u32,
    pub body: &'a str,
}

pub trait ParseNonNeg {
    fn parse_non_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized;
}

impl ParseNonNeg for u8 {
    fn parse_non_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| err.kind().clone())
            .and_then(|raw| {
                if raw != 0 && num_lit.negative {
                    Err(IntErrorKind::NegOverflow)
                } else {
                    Ok(raw)
                }
            })
    }
}

impl ParseNonNeg for usize {
    fn parse_non_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| err.kind().clone())
            .and_then(|raw| {
                if raw != 0 && num_lit.negative {
                    Err(IntErrorKind::NegOverflow)
                } else {
                    Ok(raw)
                }
            })
    }
}

pub trait ParseMaybeNeg {
    fn parse_maybe_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized;
}

impl ParseMaybeNeg for u8 {
    fn parse_maybe_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind> {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| err.kind().clone())
            .and_then(|raw| {
                if num_lit.negative {
                    i8::try_from(raw)
                        .map_err(|_| IntErrorKind::NegOverflow)
                        .map(|signed| signed.overflowing_neg().0 as Self)
                } else {
                    Ok(raw)
                }
            })
    }
}

impl ParseMaybeNeg for u16 {
    fn parse_maybe_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| err.kind().clone())
            .and_then(|raw| {
                if num_lit.negative {
                    i16::try_from(raw)
                        .map_err(|_| IntErrorKind::NegOverflow)
                        .map(|signed| signed.overflowing_neg().0 as Self)
                } else {
                    Ok(raw)
                }
            })
    }
}

impl ParseMaybeNeg for u32 {
    fn parse_maybe_neg(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| err.kind().clone())
            .and_then(|raw| {
                if num_lit.negative {
                    i32::try_from(raw)
                        .map_err(|_| IntErrorKind::NegOverflow)
                        .map(|signed| signed.overflowing_neg().0 as Self)
                } else {
                    Ok(raw)
                }
            })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Data<'a> {
    pub label: &'a str,
    pub value: DataDeclaration<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct DataDeclaration<'a> {
    pub kind: DataKind,
    pub value: DataValue<'a>,
}

#[derive(Debug, PartialEq, Eq, EnumString)]
#[strum(serialize_all = "lowercase")]
pub enum DataKind {
    Word,
    #[strum(serialize = "hword")]
    HalfWord,
    Byte,
    Ascii,
    Asciiz,
}

#[derive(Debug, PartialEq, Eq)]
pub enum DataValue<'a> {
    String(&'a str),
    Int(NumLiteral<'a>),
    Array {
        value: NumLiteral<'a>,
        size: NumLiteral<'a>,
    },
}

// TODO: include location of error
#[derive(Debug, PartialEq, Eq)]
pub enum ParseError<'a> {
    LexError(LexError),
    ParseIntError(IntErrorKind),
    UnterminatedDirective,
    UnexpectedToken(TokenKind<'a>),
    UnexpectedEOF,
    UnknownDirective(&'a str),
    UnknownInstruction(&'a str),
    UnknownDataKind(&'a str),
}

macro_rules! expect {
    ($ti:expr, $t:expr) => {{
        match $ti.next() {
            Some(t) => {
                if $t == t.kind {
                    Ok(())
                } else {
                    Err(ParseError::UnexpectedToken(t.kind))
                }
            }
            None => Err(ParseError::UnexpectedEOF),
        }
    }};
}

macro_rules! expect_ident {
    ($ti:expr) => {{
        match $ti.next() {
            Some(t) => {
                if let TokenKind::Ident(s) = t.kind {
                    Ok(s)
                } else {
                    Err(ParseError::UnexpectedToken(t.kind))
                }
            }
            None => Err(ParseError::UnexpectedEOF),
        }
    }};
}

macro_rules! expect_literal {
    ($ti:expr) => {{
        match $ti.next() {
            Some(t) => {
                if let TokenKind::Literal(l) = t.kind {
                    Ok(l)
                } else {
                    Err(ParseError::UnexpectedToken(t.kind))
                }
            }
            None => Err(ParseError::UnexpectedEOF),
        }
    }};
}

macro_rules! skip_whitespace {
    ($ti:expr) => {{
        while let Some(&TokenKind::Whitespace) = $ti.peek().map(|t| &t.kind) {
            $ti.next();
        }
    }};
}

macro_rules! skip_at_least_one_whitespace {
    ($ti:expr) => {{
        match $ti.peek().map(|t| &t.kind) {
            Some(TokenKind::Whitespace) => Ok(skip_whitespace!($ti)),
            None => Err(ParseError::UnexpectedEOF),
            Some(_) => Err(ParseError::UnexpectedToken($ti.next().unwrap().kind)),
        }
    }};
}

pub fn parse(input: &str) -> Result<Ast, ParseError> {
    let mut a = Ast::new();
    let mut cs: Option<Section> = None;

    // TODO: elide comments on a type level, i.e. maybe have a second level of
    // nested enums for whether the token is a comment, and drill down to the
    // set of enums that contain no comments here so we don't have to have
    // panics in match statements for when comments are encountered all over the
    // place.
    let mut ti = lex(input)
        .map_err(ParseError::LexError)?
        .into_iter()
        .filter(|t| match t.kind {
            TokenKind::Comment(_) => false,
            _ => true,
        })
        .peekable();

    while let Some(t) = ti.next() {
        match t.kind {
            TokenKind::Dot => {
                let tn = ti.next().ok_or(ParseError::UnterminatedDirective)?;
                if let Some(s) = cs.take() {
                    a.sections.push(s);
                }
                match tn.kind {
                    TokenKind::Ident("data") => cs = Some(Section::Data(Vec::new())),
                    TokenKind::Ident("text") => cs = Some(Section::Text(Vec::new())),
                    TokenKind::Ident(d) => return Err(ParseError::UnknownDirective(d)),
                    _ => return Err(ParseError::UnexpectedToken(tn.kind)),
                }
                skip_whitespace!(ti);
                expect!(ti, TokenKind::Newline)?;
            }
            TokenKind::Comma => todo!(),
            TokenKind::Colon => todo!(),
            TokenKind::OpenParen => todo!(),
            TokenKind::CloseParen => todo!(),
            TokenKind::Dollar => todo!(),
            TokenKind::Whitespace => {}
            TokenKind::Newline => {}
            TokenKind::Ident(i) => {
                match cs.as_mut() {
                    Some(Section::Data(data)) => {
                        // It can only be a label
                        expect!(ti, TokenKind::Colon)?;
                        skip_whitespace!(ti);
                        expect!(ti, TokenKind::Dot)?;
                        let kind_str = expect_ident!(ti)?;
                        let kind: DataKind = DataKind::try_from(kind_str)
                            .or_else(|_| Err(ParseError::UnknownDataKind(kind_str)))?;
                        skip_at_least_one_whitespace!(ti)?;
                        data.push(Data {
                            label: i,
                            value: DataDeclaration {
                                kind,
                                value: match ti.next().ok_or(ParseError::UnexpectedEOF)?.kind {
                                    TokenKind::Dot => todo!(),
                                    TokenKind::Comma => todo!(),
                                    TokenKind::Colon => todo!(),
                                    TokenKind::OpenParen => todo!(),
                                    TokenKind::CloseParen => todo!(),
                                    TokenKind::Dollar => todo!(),
                                    TokenKind::Whitespace => todo!(),
                                    TokenKind::Newline => todo!(),
                                    TokenKind::Ident(_) => todo!(),
                                    TokenKind::Literal(Literal::Num(value)) => {
                                        skip_whitespace!(ti);
                                        match ti.next().map(|t| t.kind) {
                                            None => todo!(),
                                            Some(TokenKind::Dot) => todo!(),
                                            Some(TokenKind::Comma) => todo!(),
                                            Some(TokenKind::Colon) => {
                                                skip_whitespace!(ti);
                                                match expect_literal!(ti)? {
                                                    Literal::Num(size) => {
                                                        // TODO: translate and populate this
                                                        DataValue::Array { value, size }
                                                    }
                                                    Literal::Char(_) => todo!(),
                                                    Literal::Str(_) => todo!(),
                                                }
                                            }
                                            Some(TokenKind::OpenParen) => todo!(),
                                            Some(TokenKind::CloseParen) => todo!(),
                                            Some(TokenKind::Dollar) => todo!(),
                                            Some(TokenKind::Whitespace) => todo!(),
                                            Some(TokenKind::Newline) => DataValue::Int(value),
                                            Some(TokenKind::Ident(_)) => todo!(),
                                            Some(TokenKind::Literal(_)) => todo!(),

                                            Some(TokenKind::Comment(_)) => panic!(),
                                        }
                                    }
                                    TokenKind::Literal(Literal::Char(_)) => todo!(),
                                    TokenKind::Literal(Literal::Str(s)) => DataValue::String(s),

                                    TokenKind::Comment(_) => panic!(),
                                },
                            },
                        })
                    }
                    Some(Section::Text(entries)) => {
                        // We might get a label or an instruction

                        if Some(&TokenKind::Colon) == ti.peek().map(|t| &t.kind) {
                            // This is a label
                            ti.next().unwrap();
                            entries.push(Entry::Label(i))
                        } else {
                            // This is an instruction
                            let mut inst = Instruction {
                                name: i,
                                arguments: Vec::new(),
                            };

                            skip_whitespace!(ti);
                            match ti.next().map(|t| t.kind) {
                                Some(TokenKind::Newline) | None => {
                                    entries.push(Entry::Instruction(inst));
                                    continue;
                                }
                                Some(TokenKind::Dollar) => {
                                    inst.arguments.push(Argument::Register(expect_ident!(ti)?))
                                }
                                Some(TokenKind::Ident(i)) => {
                                    inst.arguments.push(Argument::Label(i));
                                }
                                Some(TokenKind::Literal(l)) => {
                                    inst.arguments.push(Argument::Literal(l))
                                }
                                Some(TokenKind::Dot) => todo!(),
                                Some(TokenKind::Comma) => todo!(),
                                Some(TokenKind::Colon) => todo!(),
                                Some(TokenKind::OpenParen) => todo!(),
                                Some(TokenKind::CloseParen) => todo!(),
                                Some(TokenKind::Whitespace) => todo!(),

                                Some(TokenKind::Comment(_)) => panic!(),
                            }

                            loop {
                                skip_whitespace!(ti);
                                match ti.next().map(|t| t.kind) {
                                    Some(TokenKind::Comma) => {} // Get next arg
                                    Some(TokenKind::Newline) | None => break,
                                    Some(u) => return Err(ParseError::UnexpectedToken(u)),
                                }
                                skip_whitespace!(ti);
                                match ti.next().map(|t| t.kind) {
                                    Some(TokenKind::Dollar) => {
                                        inst.arguments.push(Argument::Register(expect_ident!(ti)?));
                                    }
                                    Some(TokenKind::Ident(i)) => {
                                        inst.arguments.push(Argument::Label(i));
                                    }
                                    Some(TokenKind::Literal(Literal::Num(nl))) => {
                                        if Some(&TokenKind::OpenParen) == ti.peek().map(|t| &t.kind)
                                        {
                                            ti.next().unwrap();
                                            expect!(ti, TokenKind::Dollar)?;
                                            inst.arguments.push(Argument::OffsetRegister {
                                                offset: nl,
                                                register: expect_ident!(ti)?,
                                            });
                                            expect!(ti, TokenKind::CloseParen)?;
                                        } else {
                                            inst.arguments.push(Argument::Literal(Literal::Num(nl)))
                                        }
                                    }
                                    Some(TokenKind::Dot) => todo!(),
                                    Some(TokenKind::Comma) => todo!(),
                                    Some(TokenKind::Colon) => todo!(),
                                    Some(TokenKind::OpenParen) => todo!(),
                                    Some(TokenKind::CloseParen) => todo!(),
                                    Some(TokenKind::Whitespace) => todo!(),
                                    Some(TokenKind::Newline) => todo!(),
                                    Some(TokenKind::Literal(_)) => todo!(),
                                    None => return Err(ParseError::UnexpectedEOF),

                                    Some(TokenKind::Comment(_)) => panic!(),
                                }
                            }

                            entries.push(Entry::Instruction(inst));
                        }
                    }
                    None => todo!(),
                };
            }
            TokenKind::Literal(_) => todo!(),
            // Shouldn't be possible because we're filtering out comments above
            TokenKind::Comment(_) => panic!(),
        }
    }
    if let Some(s) = cs {
        a.sections.push(s);
    }
    Ok(a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use pretty_assertions::assert_eq;

    #[test]
    fn basic() {
        assert_eq!(
            parse(include_str!("../../test/basic.asm")).unwrap(),
            Ast {
                sections: vec![Section::Text(vec![
                    Entry::Instruction(Instruction {
                        name: "addi",
                        arguments: vec![
                            Argument::Register("t0"),
                            Argument::Register("zero"),
                            Argument::Literal(Literal::Num(NumLiteral {
                                negative: false,
                                radix: 10,
                                body: "13"
                            }))
                        ],
                    }),
                    Entry::Instruction(Instruction {
                        name: "addi",
                        arguments: vec![
                            Argument::Register("t1"),
                            Argument::Register("zero"),
                            Argument::Literal(Literal::Num(NumLiteral {
                                negative: false,
                                radix: 10,
                                body: "26"
                            }))
                        ],
                    }),
                    Entry::Instruction(Instruction {
                        name: "add",
                        arguments: vec![
                            Argument::Register("t2"),
                            Argument::Register("t0"),
                            Argument::Register("t1")
                        ],
                    })
                ])]
            }
        );
    }

    #[test]
    fn fib() {
        // TODO: update this to include the contents of literals and other
        // missing data
        assert_eq!(
            parse(include_str!("../../test/fib.asm")).unwrap(),
            Ast {
                sections: vec![
                    Section::Data(vec![
                        Data {
                            label: "fibs",
                            value: DataDeclaration {
                                kind: DataKind::Word,
                                value: DataValue::Array {
                                    value: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "0"
                                    },
                                    size: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "12"
                                    }
                                }
                            }
                        },
                        Data {
                            label: "size",
                            value: DataDeclaration {
                                kind: DataKind::Word,
                                value: DataValue::Int(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "12"
                                }),
                            }
                        }
                    ]),
                    Section::Text(vec![
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("t0"), Argument::Label("fibs")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("t5"), Argument::Label("size")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("t5"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "0"
                                    },
                                    register: "t5"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "1"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "sw",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "0"
                                    },
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "sw",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "4"
                                    },
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("t5"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: true,
                                    radix: 10,
                                    body: "2"
                                }))
                            ]
                        }),
                        Entry::Label("loop"),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("t3"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "0"
                                    },
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("t4"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "4"
                                    },
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::Register("t3"),
                                Argument::Register("t4")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "sw",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "8"
                                    },
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t0"),
                                Argument::Register("t0"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "4"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("t1"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: true,
                                    radix: 10,
                                    body: "1"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "bgtz",
                            arguments: vec![Argument::Register("t1"), Argument::Label("loop")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("a0"), Argument::Label("fibs")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("a1"),
                                Argument::Register("zero"),
                                Argument::Register("t5")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "jal",
                            arguments: vec![Argument::Label("print")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![
                                Argument::Register("v0"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "10"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        })
                    ]),
                    Section::Data(vec![
                        Data {
                            label: "space",
                            value: DataDeclaration {
                                kind: DataKind::Asciiz,
                                value: DataValue::String(" ")
                            }
                        },
                        Data {
                            label: "head",
                            value: DataDeclaration {
                                kind: DataKind::Asciiz,
                                value: DataValue::String("The Fibonacci numbers are:\\n")
                            }
                        }
                    ]),
                    Section::Text(vec![
                        Entry::Label("print"),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("t0"),
                                Argument::Register("zero"),
                                Argument::Register("a0")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("zero"),
                                Argument::Register("a1")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("a0"), Argument::Label("head")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![
                                Argument::Register("v0"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "4"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        }),
                        Entry::Label("out"),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("a0"),
                                Argument::OffsetRegister {
                                    offset: NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: "0"
                                    },
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![
                                Argument::Register("v0"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "1"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("a0"), Argument::Label("space")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![
                                Argument::Register("v0"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "4"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t0"),
                                Argument::Register("t0"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "4"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("t1"),
                                Argument::Literal(Literal::Num(NumLiteral {
                                    negative: true,
                                    radix: 10,
                                    body: "1"
                                }))
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "bgtz",
                            arguments: vec![Argument::Register("t1"), Argument::Label("out")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "jr",
                            arguments: vec![Argument::Register("ra")]
                        })
                    ])
                ]
            }
        );
    }
}

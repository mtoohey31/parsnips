#![no_std]

mod lex;
use core::num::IntErrorKind;

use lex::{lex, LexError, Token, TokenKind};

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
pub struct Section<'a> {
    pub pos: usize,
    pub kind: SectionKind<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum SectionKind<'a> {
    Data(Vec<Data<'a>>),
    Text(Vec<Entry<'a>>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Entry<'a> {
    pub pos: usize,
    pub kind: EntryKind<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EntryKind<'a> {
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

#[derive(Debug, PartialEq, Eq)]
pub struct ParseError<'a> {
    pos: usize,
    kind: ParseErrorKind<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseErrorKind<'a> {
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
    ($ti:expr, $t:expr, $pos:expr) => {{
        match $ti.next() {
            Some(t) => {
                if $t == t.kind {
                    Ok(())
                } else {
                    Err(ParseError {
                        pos: t.pos,
                        kind: ParseErrorKind::UnexpectedToken(t.kind),
                    })
                }
            }
            None => Err(ParseError {
                pos: $pos,
                kind: ParseErrorKind::UnexpectedEOF,
            }),
        }
    }};
}

macro_rules! expect_ident {
    ($ti:expr, $pos:expr) => {{
        match $ti.next() {
            Some(t) => {
                if let TokenKind::Ident(s) = t.kind {
                    Ok((t.pos, s))
                } else {
                    Err(ParseError {
                        pos: t.pos,
                        kind: ParseErrorKind::UnexpectedToken(t.kind),
                    })
                }
            }
            None => Err(ParseError {
                pos: $pos,
                kind: ParseErrorKind::UnexpectedEOF,
            }),
        }
    }};
}

macro_rules! expect_literal {
    ($ti:expr, $pos:expr) => {{
        match $ti.next() {
            Some(t) => {
                if let TokenKind::Literal(l) = t.kind {
                    Ok(l)
                } else {
                    Err(ParseError {
                        pos: t.pos,
                        kind: ParseErrorKind::UnexpectedToken(t.kind),
                    })
                }
            }
            None => Err(ParseError {
                pos: $pos,
                kind: ParseErrorKind::UnexpectedEOF,
            }),
        }
    }};
}

macro_rules! skip_whitespace {
    ($ti:expr, $pos:expr) => {{
        let mut pos = $pos;
        while let Some(&TokenKind::Whitespace) = $ti.peek().map(|t| &t.kind) {
            Token { pos, .. } = $ti.next().unwrap();
        }
        pos
    }};
}

macro_rules! skip_at_least_one_whitespace {
    ($ti:expr, $pos:expr) => {{
        match $ti.peek().map(|t| &t.kind) {
            Some(TokenKind::Whitespace) => Ok(skip_whitespace!($ti, $pos)),
            None => Err(ParseError {
                pos: $pos,
                kind: ParseErrorKind::UnexpectedEOF,
            }),
            Some(_) => {
                let t = $ti.next().unwrap();
                Err(ParseError {
                    pos: t.pos,
                    kind: ParseErrorKind::UnexpectedToken(t.kind),
                })
            }
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
        .map_err(|e| ParseError {
            pos: e.pos,
            kind: ParseErrorKind::LexError(e),
        })?
        .into_iter()
        .filter(|t| match t.kind {
            TokenKind::Comment(_) => false,
            _ => true,
        })
        .peekable();

    while let Some(t) = ti.next() {
        match t.kind {
            TokenKind::Dot => {
                let tn = ti.next().ok_or(ParseError {
                    pos: t.pos + 1,
                    kind: ParseErrorKind::UnterminatedDirective,
                })?;
                if let Some(s) = cs.take() {
                    a.sections.push(s);
                }
                match tn.kind {
                    TokenKind::Ident("data") => {
                        cs = Some(Section {
                            pos: t.pos,
                            kind: SectionKind::Data(Vec::new()),
                        })
                    }
                    TokenKind::Ident("text") => {
                        cs = Some(Section {
                            pos: t.pos,
                            kind: SectionKind::Text(Vec::new()),
                        })
                    }
                    TokenKind::Ident(d) => {
                        return Err(ParseError {
                            pos: tn.pos,
                            kind: ParseErrorKind::UnknownDirective(d),
                        })
                    }
                    _ => {
                        return Err(ParseError {
                            pos: tn.pos,
                            kind: ParseErrorKind::UnexpectedToken(tn.kind),
                        })
                    }
                }
                expect!(ti, TokenKind::Newline, skip_whitespace!(ti, tn.pos))?;
            }
            TokenKind::Comma => todo!(),
            TokenKind::Colon => todo!(),
            TokenKind::OpenParen => todo!(),
            TokenKind::CloseParen => todo!(),
            TokenKind::Dollar => todo!(),
            TokenKind::Whitespace => {}
            TokenKind::Newline => {}
            TokenKind::Ident(i) => {
                let s = match cs.as_mut() {
                    Some(s) => s,
                    None => todo!(),
                };
                match &mut s.kind {
                    SectionKind::Data(data) => {
                        // It can only be a label
                        expect!(ti, TokenKind::Colon, t.pos)?;
                        let pos = skip_whitespace!(ti, t.pos + 1);
                        expect!(ti, TokenKind::Dot, pos)?;
                        let (pos, kind_str) = expect_ident!(ti, pos + 1)?;
                        let kind: DataKind = DataKind::try_from(kind_str).or_else(|_| {
                            Err(ParseError {
                                pos,
                                kind: ParseErrorKind::UnknownDataKind(kind_str),
                            })
                        })?;
                        let pos = skip_at_least_one_whitespace!(ti, pos)?;
                        let t = ti.next().ok_or(ParseError {
                            pos,
                            kind: ParseErrorKind::UnexpectedEOF,
                        })?;
                        data.push(Data {
                            label: i,
                            value: DataDeclaration {
                                kind,
                                value: match t.kind {
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
                                        skip_whitespace!(ti, t.pos);
                                        let t = match ti.next() {
                                            Some(t) => t,
                                            None => todo!(),
                                        };
                                        match t.kind {
                                            TokenKind::Dot => todo!(),
                                            TokenKind::Comma => todo!(),
                                            TokenKind::Colon => {
                                                let pos = skip_whitespace!(ti, t.pos);
                                                match expect_literal!(ti, pos)? {
                                                    Literal::Num(size) => {
                                                        // TODO: translate and populate this
                                                        DataValue::Array { value, size }
                                                    }
                                                    Literal::Char(_) => todo!(),
                                                    Literal::Str(_) => todo!(),
                                                }
                                            }
                                            TokenKind::OpenParen => todo!(),
                                            TokenKind::CloseParen => todo!(),
                                            TokenKind::Dollar => todo!(),
                                            TokenKind::Whitespace => todo!(),
                                            TokenKind::Newline => DataValue::Int(value),
                                            TokenKind::Ident(_) => todo!(),
                                            TokenKind::Literal(_) => todo!(),

                                            TokenKind::Comment(_) => panic!(),
                                        }
                                    }
                                    TokenKind::Literal(Literal::Char(_)) => todo!(),
                                    TokenKind::Literal(Literal::Str(s)) => DataValue::String(s),

                                    TokenKind::Comment(_) => panic!(),
                                },
                            },
                        })
                    }
                    SectionKind::Text(entries) => {
                        // We might get a label or an instruction

                        if Some(&TokenKind::Colon) == ti.peek().map(|t| &t.kind) {
                            // This is a label
                            ti.next().unwrap();
                            entries.push(Entry {
                                pos: t.pos,
                                kind: EntryKind::Label(i),
                            })
                        } else {
                            // This is an instruction
                            let mut inst = Instruction {
                                name: i,
                                arguments: Vec::new(),
                            };

                            let pos = skip_whitespace!(ti, t.pos);
                            let tn = match ti.next() {
                                Some(t) => t,
                                None => {
                                    entries.push(Entry {
                                        pos: t.pos,
                                        kind: EntryKind::Instruction(inst),
                                    });
                                    continue;
                                }
                            };
                            match tn.kind {
                                TokenKind::Newline => {
                                    entries.push(Entry {
                                        pos: t.pos,
                                        kind: EntryKind::Instruction(inst),
                                    });
                                    continue;
                                }
                                TokenKind::Dollar => inst
                                    .arguments
                                    .push(Argument::Register(expect_ident!(ti, tn.pos)?.1)),
                                TokenKind::Ident(i) => {
                                    inst.arguments.push(Argument::Label(i));
                                }
                                TokenKind::Literal(l) => inst.arguments.push(Argument::Literal(l)),
                                TokenKind::Dot => todo!(),
                                TokenKind::Comma => todo!(),
                                TokenKind::Colon => todo!(),
                                TokenKind::OpenParen => todo!(),
                                TokenKind::CloseParen => todo!(),
                                TokenKind::Whitespace => todo!(),

                                TokenKind::Comment(_) => panic!(),
                            }

                            loop {
                                let pos = skip_whitespace!(ti, pos);
                                let t = match ti.next() {
                                    Some(t) => t,
                                    None => {
                                        break;
                                    }
                                };
                                match t.kind {
                                    TokenKind::Comma => {} // Get next arg
                                    TokenKind::Newline => break,
                                    u => {
                                        return Err(ParseError {
                                            pos,
                                            kind: ParseErrorKind::UnexpectedToken(u),
                                        })
                                    }
                                };

                                let pos = skip_whitespace!(ti, t.pos);
                                let t = match ti.next() {
                                    Some(t) => t,
                                    None => {
                                        return Err(ParseError {
                                            pos,
                                            kind: ParseErrorKind::UnexpectedEOF,
                                        });
                                    }
                                };
                                match t.kind {
                                    TokenKind::Dollar => {
                                        inst.arguments
                                            .push(Argument::Register(expect_ident!(ti, t.pos)?.1));
                                    }
                                    TokenKind::Ident(i) => {
                                        inst.arguments.push(Argument::Label(i));
                                    }
                                    TokenKind::Literal(Literal::Num(nl)) => {
                                        if Some(&TokenKind::OpenParen) == ti.peek().map(|t| &t.kind)
                                        {
                                            let Token { pos, .. } = ti.next().unwrap();
                                            expect!(ti, TokenKind::Dollar, pos)?;
                                            let (pos, register) = expect_ident!(ti, pos + 1)?;
                                            inst.arguments.push(Argument::OffsetRegister {
                                                offset: nl,
                                                register,
                                            });
                                            expect!(ti, TokenKind::CloseParen, pos)?;
                                        } else {
                                            inst.arguments.push(Argument::Literal(Literal::Num(nl)))
                                        }
                                    }
                                    TokenKind::Dot => todo!(),
                                    TokenKind::Comma => todo!(),
                                    TokenKind::Colon => todo!(),
                                    TokenKind::OpenParen => todo!(),
                                    TokenKind::CloseParen => todo!(),
                                    TokenKind::Whitespace => todo!(),
                                    TokenKind::Newline => todo!(),
                                    TokenKind::Literal(_) => todo!(),

                                    TokenKind::Comment(_) => panic!(),
                                }
                            }

                            entries.push(Entry {
                                pos: t.pos,
                                kind: EntryKind::Instruction(inst),
                            });
                        }
                    }
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
                sections: vec![Section {
                    pos: 6,
                    kind: SectionKind::Text(vec![
                        Entry {
                            pos: 18,
                            kind: EntryKind::Instruction(Instruction {
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
                            })
                        },
                        Entry {
                            pos: 44,
                            kind: EntryKind::Instruction(Instruction {
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
                            })
                        },
                        Entry {
                            pos: 70,
                            kind: EntryKind::Instruction(Instruction {
                                name: "add",
                                arguments: vec![
                                    Argument::Register("t2"),
                                    Argument::Register("t0"),
                                    Argument::Register("t1")
                                ],
                            })
                        }
                    ])
                }]
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
                    Section {
                        pos: 138,
                        kind: SectionKind::Data(vec![
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
                        ])
                    },
                    Section {
                        pos: 269,
                        kind: SectionKind::Text(vec![
                            Entry {
                                pos: 281,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    arguments: vec![
                                        Argument::Register("t0"),
                                        Argument::Label("fibs")
                                    ]
                                })
                            },
                            Entry {
                                pos: 333,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    arguments: vec![
                                        Argument::Register("t5"),
                                        Argument::Label("size")
                                    ]
                                })
                            },
                            Entry {
                                pos: 393,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 439,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    arguments: vec![
                                        Argument::Register("t2"),
                                        Argument::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "1"
                                        }))
                                    ]
                                })
                            },
                            Entry {
                                pos: 503,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 542,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 588,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 658,
                                kind: EntryKind::Label("loop")
                            },
                            Entry {
                                pos: 664,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 721,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 779,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    arguments: vec![
                                        Argument::Register("t2"),
                                        Argument::Register("t3"),
                                        Argument::Register("t4")
                                    ]
                                })
                            },
                            Entry {
                                pos: 829,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 897,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 967,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 1020,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "bgtz",
                                    arguments: vec![
                                        Argument::Register("t1"),
                                        Argument::Label("loop")
                                    ]
                                })
                            },
                            Entry {
                                pos: 1078,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    arguments: vec![
                                        Argument::Register("a0"),
                                        Argument::Label("fibs")
                                    ]
                                })
                            },
                            Entry {
                                pos: 1141,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    arguments: vec![
                                        Argument::Register("a1"),
                                        Argument::Register("zero"),
                                        Argument::Register("t5")
                                    ]
                                })
                            },
                            Entry {
                                pos: 1204,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "jal",
                                    arguments: vec![Argument::Label("print")]
                                })
                            },
                            Entry {
                                pos: 1255,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    arguments: vec![
                                        Argument::Register("v0"),
                                        Argument::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "10"
                                        }))
                                    ]
                                })
                            },
                            Entry {
                                pos: 1306,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    arguments: vec![]
                                })
                            }
                        ])
                    },
                    Section {
                        pos: 1414,
                        kind: SectionKind::Data(vec![
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
                        ])
                    },
                    Section {
                        pos: 1534,
                        kind: SectionKind::Text(vec![
                            Entry {
                                pos: 1540,
                                kind: EntryKind::Label("print")
                            },
                            Entry {
                                pos: 1546,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    arguments: vec![
                                        Argument::Register("t0"),
                                        Argument::Register("zero"),
                                        Argument::Register("a0")
                                    ]
                                })
                            },
                            Entry {
                                pos: 1602,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    arguments: vec![
                                        Argument::Register("t1"),
                                        Argument::Register("zero"),
                                        Argument::Register("a1")
                                    ]
                                })
                            },
                            Entry {
                                pos: 1670,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    arguments: vec![
                                        Argument::Register("a0"),
                                        Argument::Label("head")
                                    ]
                                })
                            },
                            Entry {
                                pos: 1730,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    arguments: vec![
                                        Argument::Register("v0"),
                                        Argument::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "4"
                                        }))
                                    ]
                                })
                            },
                            Entry {
                                pos: 1789,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    arguments: vec![]
                                })
                            },
                            Entry {
                                pos: 1827,
                                kind: EntryKind::Label("out")
                            },
                            Entry {
                                pos: 1833,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 1897,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    arguments: vec![
                                        Argument::Register("v0"),
                                        Argument::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "1"
                                        }))
                                    ]
                                })
                            },
                            Entry {
                                pos: 1957,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    arguments: vec![]
                                })
                            },
                            Entry {
                                pos: 2010,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    arguments: vec![
                                        Argument::Register("a0"),
                                        Argument::Label("space")
                                    ]
                                })
                            },
                            Entry {
                                pos: 2075,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    arguments: vec![
                                        Argument::Register("v0"),
                                        Argument::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "4"
                                        }))
                                    ]
                                })
                            },
                            Entry {
                                pos: 2134,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    arguments: vec![]
                                })
                            },
                            Entry {
                                pos: 2178,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 2226,
                                kind: EntryKind::Instruction(Instruction {
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
                                })
                            },
                            Entry {
                                pos: 2279,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "bgtz",
                                    arguments: vec![
                                        Argument::Register("t1"),
                                        Argument::Label("out")
                                    ]
                                })
                            },
                            Entry {
                                pos: 2332,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "jr",
                                    arguments: vec![Argument::Register("ra")]
                                })
                            }
                        ])
                    }
                ]
            }
        );
    }
}

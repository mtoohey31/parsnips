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
    pub eof_pos: usize,
}

impl Ast<'_> {
    fn new(eof_pos: usize) -> Self {
        Self {
            sections: Vec::new(),
            eof_pos,
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
    pub args: Vec<Argument<'a>>,
    // the position of the final newline, or the EOF, which is needed for showing errors when
    // arguments are missing
    pub end_pos: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Argument<'a> {
    pub pos: usize,
    pub kind: ArgumentKind<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ArgumentKind<'a> {
    Register(&'a str),
    OffsetRegister {
        // the position of the offset is equal to the position of this argument
        // as whole, so we don't need to store it again here
        offset: NumLiteral<'a>,
        register_pos: usize,
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
    pub pos: usize,
    pub label: &'a str,
    pub value: DataDeclaration<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct DataDeclaration<'a> {
    pub pos: usize,
    pub kind: DataKind,
    pub value_pos: usize,
    pub value: DataValue<'a>,
}

#[derive(Debug, PartialEq, Eq, EnumString)]
#[strum(serialize_all = "lowercase")]
pub enum DataKind {
    Word,
    #[strum(serialize = "hword", serialize = "half")]
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
        size_pos: usize,
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
                    Ok((s, t.pos))
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
                    Ok((l, t.pos))
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
    let mut a = Ast::new(input.len());
    let mut cs: Option<Section> = None;

    let mut ti = lex(input)
        .map_err(|e| ParseError {
            pos: e.pos,
            kind: ParseErrorKind::LexError(e),
        })?
        .into_iter()
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
                        let (kind_str, pos) = expect_ident!(ti, pos + 1)?;
                        let dot_pos = pos - 1;
                        let kind: DataKind = DataKind::try_from(kind_str).or_else(|_| {
                            Err(ParseError {
                                pos,
                                kind: ParseErrorKind::UnknownDataKind(kind_str),
                            })
                        })?;
                        let pos = skip_at_least_one_whitespace!(ti, pos)?;
                        let tn = ti.next().ok_or(ParseError {
                            pos,
                            kind: ParseErrorKind::UnexpectedEOF,
                        })?;
                        data.push(Data {
                            pos: t.pos,
                            label: i,
                            value: DataDeclaration {
                                pos: dot_pos,
                                kind,
                                value_pos: tn.pos,
                                value: match tn.kind {
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
                                        skip_whitespace!(ti, tn.pos);
                                        let t = match ti.next() {
                                            Some(t) => t,
                                            None => todo!(),
                                        };
                                        match t.kind {
                                            TokenKind::Dot => todo!(),
                                            TokenKind::Comma => todo!(),
                                            TokenKind::Colon => {
                                                let pos = skip_whitespace!(ti, t.pos);
                                                let (size_lit, size_pos) =
                                                    expect_literal!(ti, pos)?;
                                                match size_lit {
                                                    Literal::Num(size) => DataValue::Array {
                                                        value,
                                                        size_pos,
                                                        size,
                                                    },
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
                                        }
                                    }
                                    TokenKind::Literal(Literal::Char(_)) => todo!(),
                                    TokenKind::Literal(Literal::Str(s)) => DataValue::String(s),
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
                            let entry_pos = t.pos;
                            // This is an instruction
                            let name = i;
                            let mut args = Vec::new();

                            let pos = skip_whitespace!(ti, t.pos);
                            let tn = match ti.next() {
                                Some(t) => t,
                                None => {
                                    entries.push(Entry {
                                        pos: entry_pos,
                                        kind: EntryKind::Instruction(Instruction {
                                            name,
                                            args,
                                            end_pos: pos,
                                        }),
                                    });
                                    continue;
                                }
                            };
                            match tn.kind {
                                TokenKind::Newline => {
                                    entries.push(Entry {
                                        pos: entry_pos,
                                        kind: EntryKind::Instruction(Instruction {
                                            name,
                                            args,
                                            end_pos: tn.pos,
                                        }),
                                    });
                                    continue;
                                }
                                TokenKind::Dollar => args.push(Argument {
                                    pos: tn.pos,
                                    kind: ArgumentKind::Register(expect_ident!(ti, tn.pos)?.0),
                                }),
                                TokenKind::Ident(i) => {
                                    args.push(Argument {
                                        pos: tn.pos,
                                        kind: ArgumentKind::Label(i),
                                    });
                                }
                                TokenKind::Literal(l) => args.push(Argument {
                                    pos: tn.pos,
                                    kind: ArgumentKind::Literal(l),
                                }),
                                TokenKind::Dot => todo!(),
                                TokenKind::Comma => todo!(),
                                TokenKind::Colon => todo!(),
                                TokenKind::OpenParen => todo!(),
                                TokenKind::CloseParen => todo!(),
                                TokenKind::Whitespace => todo!(),
                            }

                            loop {
                                let pos = skip_whitespace!(ti, pos);
                                let t = match ti.next() {
                                    Some(t) => t,
                                    None => {
                                        entries.push(Entry {
                                            pos: entry_pos,
                                            kind: EntryKind::Instruction(Instruction {
                                                name,
                                                args,
                                                end_pos: pos,
                                            }),
                                        });
                                        break;
                                    }
                                };
                                match t.kind {
                                    TokenKind::Comma => {} // Get next arg
                                    TokenKind::Newline => {
                                        entries.push(Entry {
                                            pos: entry_pos,
                                            kind: EntryKind::Instruction(Instruction {
                                                name,
                                                args,
                                                end_pos: t.pos,
                                            }),
                                        });
                                        break;
                                    }
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
                                        args.push(Argument {
                                            pos: t.pos,
                                            kind: ArgumentKind::Register(
                                                expect_ident!(ti, t.pos)?.0,
                                            ),
                                        });
                                    }
                                    TokenKind::Ident(i) => {
                                        args.push(Argument {
                                            pos: t.pos,
                                            kind: ArgumentKind::Label(i),
                                        });
                                    }
                                    TokenKind::Literal(Literal::Num(nl)) => {
                                        if Some(&TokenKind::OpenParen) == ti.peek().map(|t| &t.kind)
                                        {
                                            let Token { pos, .. } = ti.next().unwrap();
                                            expect!(ti, TokenKind::Dollar, pos)?;
                                            let (register, ident_pos) = expect_ident!(ti, pos + 1)?;
                                            args.push(Argument {
                                                pos: t.pos,
                                                kind: ArgumentKind::OffsetRegister {
                                                    offset: nl,
                                                    register_pos: pos + 1,
                                                    register,
                                                },
                                            });
                                            expect!(ti, TokenKind::CloseParen, ident_pos)?;
                                        } else {
                                            args.push(Argument {
                                                pos: t.pos,
                                                kind: ArgumentKind::Literal(Literal::Num(nl)),
                                            })
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
                                }
                            }
                        }
                    }
                };
            }
            TokenKind::Literal(_) => todo!(),
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
                                args: vec![
                                    Argument {
                                        pos: 23,
                                        kind: ArgumentKind::Register("t0")
                                    },
                                    Argument {
                                        pos: 28,
                                        kind: ArgumentKind::Register("zero")
                                    },
                                    Argument {
                                        pos: 35,
                                        kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "13"
                                        }))
                                    }
                                ],
                                end_pos: 37,
                            })
                        },
                        Entry {
                            pos: 44,
                            kind: EntryKind::Instruction(Instruction {
                                name: "addi",
                                args: vec![
                                    Argument {
                                        pos: 49,
                                        kind: ArgumentKind::Register("t1")
                                    },
                                    Argument {
                                        pos: 54,
                                        kind: ArgumentKind::Register("zero")
                                    },
                                    Argument {
                                        pos: 61,
                                        kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "26"
                                        }))
                                    }
                                ],
                                end_pos: 63,
                            })
                        },
                        Entry {
                            pos: 70,
                            kind: EntryKind::Instruction(Instruction {
                                name: "add",
                                args: vec![
                                    Argument {
                                        pos: 74,
                                        kind: ArgumentKind::Register("t2")
                                    },
                                    Argument {
                                        pos: 79,
                                        kind: ArgumentKind::Register("t0")
                                    },
                                    Argument {
                                        pos: 84,
                                        kind: ArgumentKind::Register("t1")
                                    }
                                ],
                                end_pos: 87,
                            })
                        }
                    ])
                }],
                eof_pos: 88
            }
        );
    }

    #[test]
    fn fib() {
        assert_eq!(
            parse(include_str!("../../test/fib.asm")).unwrap(),
            Ast {
                sections: vec![
                    Section {
                        pos: 138,
                        kind: SectionKind::Data(vec![
                            Data {
                                pos: 144,
                                label: "fibs",
                                value: DataDeclaration {
                                    pos: 150,
                                    kind: DataKind::Word,
                                    value_pos: 158,
                                    value: DataValue::Array {
                                        value: NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "0"
                                        },
                                        size_pos: 162,
                                        size: NumLiteral {
                                            negative: false,
                                            radix: 10,
                                            body: "12"
                                        }
                                    }
                                }
                            },
                            Data {
                                pos: 216,
                                label: "size",
                                value: DataDeclaration {
                                    pos: 222,
                                    kind: DataKind::Word,
                                    value_pos: 229,
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
                                    args: vec![
                                        Argument {
                                            pos: 286,
                                            kind: ArgumentKind::Register("t0")
                                        },
                                        Argument {
                                            pos: 291,
                                            kind: ArgumentKind::Label("fibs")
                                        }
                                    ],
                                    end_pos: 326,
                                })
                            },
                            Entry {
                                pos: 333,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    args: vec![
                                        Argument {
                                            pos: 338,
                                            kind: ArgumentKind::Register("t5")
                                        },
                                        Argument {
                                            pos: 343,
                                            kind: ArgumentKind::Label("size")
                                        }
                                    ],
                                    end_pos: 386,
                                })
                            },
                            Entry {
                                pos: 393,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "lw",
                                    args: vec![
                                        Argument {
                                            pos: 398,
                                            kind: ArgumentKind::Register("t5")
                                        },
                                        Argument {
                                            pos: 403,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "0"
                                                },
                                                register_pos: 405,
                                                register: "t5"
                                            }
                                        }
                                    ],
                                    end_pos: 432,
                                })
                            },
                            Entry {
                                pos: 439,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    args: vec![
                                        Argument {
                                            pos: 444,
                                            kind: ArgumentKind::Register("t2")
                                        },
                                        Argument {
                                            pos: 449,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "1"
                                            }))
                                        }
                                    ],
                                    end_pos: 496,
                                })
                            },
                            Entry {
                                pos: 503,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "sw",
                                    args: vec![
                                        Argument {
                                            pos: 508,
                                            kind: ArgumentKind::Register("t2")
                                        },
                                        Argument {
                                            pos: 513,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "0"
                                                },
                                                register_pos: 515,
                                                register: "t0"
                                            }
                                        }
                                    ],
                                    end_pos: 535,
                                })
                            },
                            Entry {
                                pos: 542,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "sw",
                                    args: vec![
                                        Argument {
                                            pos: 547,
                                            kind: ArgumentKind::Register("t2")
                                        },
                                        Argument {
                                            pos: 552,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "4"
                                                },
                                                register_pos: 554,
                                                register: "t0"
                                            }
                                        }
                                    ],
                                    end_pos: 581,
                                })
                            },
                            Entry {
                                pos: 588,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "addi",
                                    args: vec![
                                        Argument {
                                            pos: 593,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 598,
                                            kind: ArgumentKind::Register("t5")
                                        },
                                        Argument {
                                            pos: 603,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: true,
                                                radix: 10,
                                                body: "2"
                                            }))
                                        }
                                    ],
                                    end_pos: 657,
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
                                    args: vec![
                                        Argument {
                                            pos: 669,
                                            kind: ArgumentKind::Register("t3")
                                        },
                                        Argument {
                                            pos: 674,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "0"
                                                },
                                                register_pos: 676,
                                                register: "t0"
                                            }
                                        }
                                    ],
                                    end_pos: 714,
                                })
                            },
                            Entry {
                                pos: 721,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "lw",
                                    args: vec![
                                        Argument {
                                            pos: 726,
                                            kind: ArgumentKind::Register("t4")
                                        },
                                        Argument {
                                            pos: 731,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "4"
                                                },
                                                register_pos: 733,
                                                register: "t0"
                                            }
                                        }
                                    ],
                                    end_pos: 772,
                                })
                            },
                            Entry {
                                pos: 779,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    args: vec![
                                        Argument {
                                            pos: 784,
                                            kind: ArgumentKind::Register("t2")
                                        },
                                        Argument {
                                            pos: 789,
                                            kind: ArgumentKind::Register("t3")
                                        },
                                        Argument {
                                            pos: 794,
                                            kind: ArgumentKind::Register("t4")
                                        }
                                    ],
                                    end_pos: 822,
                                })
                            },
                            Entry {
                                pos: 829,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "sw",
                                    args: vec![
                                        Argument {
                                            pos: 834,
                                            kind: ArgumentKind::Register("t2")
                                        },
                                        Argument {
                                            pos: 839,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "8"
                                                },
                                                register_pos: 841,
                                                register: "t0"
                                            }
                                        }
                                    ],
                                    end_pos: 890,
                                })
                            },
                            Entry {
                                pos: 897,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "addi",
                                    args: vec![
                                        Argument {
                                            pos: 902,
                                            kind: ArgumentKind::Register("t0")
                                        },
                                        Argument {
                                            pos: 907,
                                            kind: ArgumentKind::Register("t0")
                                        },
                                        Argument {
                                            pos: 912,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "4"
                                            }))
                                        }
                                    ],
                                    end_pos: 960,
                                })
                            },
                            Entry {
                                pos: 967,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "addi",
                                    args: vec![
                                        Argument {
                                            pos: 972,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 977,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 982,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: true,
                                                radix: 10,
                                                body: "1"
                                            }))
                                        }
                                    ],
                                    end_pos: 1013,
                                })
                            },
                            Entry {
                                pos: 1020,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "bgtz",
                                    args: vec![
                                        Argument {
                                            pos: 1025,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 1030,
                                            kind: ArgumentKind::Label("loop")
                                        }
                                    ],
                                    end_pos: 1071,
                                })
                            },
                            Entry {
                                pos: 1078,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    args: vec![
                                        Argument {
                                            pos: 1083,
                                            kind: ArgumentKind::Register("a0")
                                        },
                                        Argument {
                                            pos: 1088,
                                            kind: ArgumentKind::Label("fibs")
                                        }
                                    ],
                                    end_pos: 1134,
                                })
                            },
                            Entry {
                                pos: 1141,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    args: vec![
                                        Argument {
                                            pos: 1146,
                                            kind: ArgumentKind::Register("a1")
                                        },
                                        Argument {
                                            pos: 1151,
                                            kind: ArgumentKind::Register("zero")
                                        },
                                        Argument {
                                            pos: 1158,
                                            kind: ArgumentKind::Register("t5")
                                        }
                                    ],
                                    end_pos: 1197,
                                })
                            },
                            Entry {
                                pos: 1204,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "jal",
                                    args: vec![Argument {
                                        pos: 1209,
                                        kind: ArgumentKind::Label("print")
                                    }],
                                    end_pos: 1248,
                                })
                            },
                            Entry {
                                pos: 1255,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    args: vec![
                                        Argument {
                                            pos: 1260,
                                            kind: ArgumentKind::Register("v0")
                                        },
                                        Argument {
                                            pos: 1265,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "10"
                                            }))
                                        }
                                    ],
                                    end_pos: 1299,
                                })
                            },
                            Entry {
                                pos: 1306,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    args: vec![],
                                    end_pos: 1349,
                                })
                            }
                        ])
                    },
                    Section {
                        pos: 1414,
                        kind: SectionKind::Data(vec![
                            Data {
                                pos: 1420,
                                label: "space",
                                value: DataDeclaration {
                                    pos: 1426,
                                    kind: DataKind::Asciiz,
                                    value_pos: 1435,
                                    value: DataValue::String(" ")
                                }
                            },
                            Data {
                                pos: 1482,
                                label: "head",
                                value: DataDeclaration {
                                    pos: 1488,
                                    kind: DataKind::Asciiz,
                                    value_pos: 1497,
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
                                    args: vec![
                                        Argument {
                                            pos: 1551,
                                            kind: ArgumentKind::Register("t0")
                                        },
                                        Argument {
                                            pos: 1556,
                                            kind: ArgumentKind::Register("zero")
                                        },
                                        Argument {
                                            pos: 1563,
                                            kind: ArgumentKind::Register("a0")
                                        }
                                    ],
                                    end_pos: 1595,
                                })
                            },
                            Entry {
                                pos: 1602,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "add",
                                    args: vec![
                                        Argument {
                                            pos: 1607,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 1612,
                                            kind: ArgumentKind::Register("zero")
                                        },
                                        Argument {
                                            pos: 1619,
                                            kind: ArgumentKind::Register("a1")
                                        }
                                    ],
                                    end_pos: 1663,
                                })
                            },
                            Entry {
                                pos: 1670,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    args: vec![
                                        Argument {
                                            pos: 1675,
                                            kind: ArgumentKind::Register("a0")
                                        },
                                        Argument {
                                            pos: 1680,
                                            kind: ArgumentKind::Label("head")
                                        }
                                    ],
                                    end_pos: 1723,
                                })
                            },
                            Entry {
                                pos: 1730,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    args: vec![
                                        Argument {
                                            pos: 1735,
                                            kind: ArgumentKind::Register("v0")
                                        },
                                        Argument {
                                            pos: 1740,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "4"
                                            }))
                                        }
                                    ],
                                    end_pos: 1782,
                                })
                            },
                            Entry {
                                pos: 1789,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    args: vec![],
                                    end_pos: 1826,
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
                                    args: vec![
                                        Argument {
                                            pos: 1838,
                                            kind: ArgumentKind::Register("a0")
                                        },
                                        Argument {
                                            pos: 1843,
                                            kind: ArgumentKind::OffsetRegister {
                                                offset: NumLiteral {
                                                    negative: false,
                                                    radix: 10,
                                                    body: "0"
                                                },
                                                register_pos: 1845,
                                                register: "t0"
                                            }
                                        }
                                    ],
                                    end_pos: 1890,
                                })
                            },
                            Entry {
                                pos: 1897,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    args: vec![
                                        Argument {
                                            pos: 1902,
                                            kind: ArgumentKind::Register("v0")
                                        },
                                        Argument {
                                            pos: 1907,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "1"
                                            }))
                                        }
                                    ],
                                    end_pos: 1950,
                                })
                            },
                            Entry {
                                pos: 1957,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    args: vec![],
                                    end_pos: 2003,
                                })
                            },
                            Entry {
                                pos: 2010,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "la",
                                    args: vec![
                                        Argument {
                                            pos: 2015,
                                            kind: ArgumentKind::Register("a0")
                                        },
                                        Argument {
                                            pos: 2020,
                                            kind: ArgumentKind::Label("space")
                                        }
                                    ],
                                    end_pos: 2068,
                                })
                            },
                            Entry {
                                pos: 2075,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "li",
                                    args: vec![
                                        Argument {
                                            pos: 2080,
                                            kind: ArgumentKind::Register("v0")
                                        },
                                        Argument {
                                            pos: 2085,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "4"
                                            }))
                                        }
                                    ],
                                    end_pos: 2127,
                                })
                            },
                            Entry {
                                pos: 2134,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "syscall",
                                    args: vec![],
                                    end_pos: 2171,
                                })
                            },
                            Entry {
                                pos: 2178,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "addi",
                                    args: vec![
                                        Argument {
                                            pos: 2183,
                                            kind: ArgumentKind::Register("t0")
                                        },
                                        Argument {
                                            pos: 2188,
                                            kind: ArgumentKind::Register("t0")
                                        },
                                        Argument {
                                            pos: 2193,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: false,
                                                radix: 10,
                                                body: "4"
                                            }))
                                        }
                                    ],
                                    end_pos: 2219,
                                })
                            },
                            Entry {
                                pos: 2226,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "addi",
                                    args: vec![
                                        Argument {
                                            pos: 2231,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 2236,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 2241,
                                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                                negative: true,
                                                radix: 10,
                                                body: "1"
                                            }))
                                        }
                                    ],
                                    end_pos: 2272,
                                })
                            },
                            Entry {
                                pos: 2279,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "bgtz",
                                    args: vec![
                                        Argument {
                                            pos: 2284,
                                            kind: ArgumentKind::Register("t1")
                                        },
                                        Argument {
                                            pos: 2289,
                                            kind: ArgumentKind::Label("out")
                                        }
                                    ],
                                    end_pos: 2325,
                                })
                            },
                            Entry {
                                pos: 2332,
                                kind: EntryKind::Instruction(Instruction {
                                    name: "jr",
                                    args: vec![Argument {
                                        pos: 2337,
                                        kind: ArgumentKind::Register("ra")
                                    }],
                                    end_pos: 2362,
                                })
                            }
                        ])
                    }
                ],
                eof_pos: 2365
            }
        );
    }
}

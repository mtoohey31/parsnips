#![no_std]
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

mod lex;
use core::num::IntErrorKind;

use lex::{lex, LexError, Token, TokenKind};

extern crate alloc;
use alloc::vec::Vec;
use parsnips_util::UnreachableUnwrap;
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
#[cfg_attr(test, derive(Clone, Copy))]
pub enum Literal<'a> {
    Num(NumLiteral<'a>),
    Char(char),
    Str(&'a str),
}

#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(test, derive(Copy))]
pub struct NumLiteral<'a> {
    // this is a field because we can't take a slice of the input that
    // includes just the sign and the number body when there's a 0b, 0o, 0x
    // prefix
    pub negative: bool,
    pub radix: u32,
    pub body: &'a str,
}

pub trait ParseUnsigned {
    fn parse_unsigned(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized;
}

impl ParseUnsigned for u8 {
    fn parse_unsigned(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
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

impl ParseUnsigned for usize {
    fn parse_unsigned(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
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

pub trait ParseMaybeSigned {
    fn parse_maybe_signed(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized;
}

impl ParseMaybeSigned for u8 {
    fn parse_maybe_signed(num_lit: NumLiteral) -> Result<Self, IntErrorKind> {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| {
                if err.kind() == &IntErrorKind::PosOverflow && num_lit.negative {
                    IntErrorKind::NegOverflow
                } else {
                    err.kind().clone()
                }
            })
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

impl ParseMaybeSigned for u16 {
    fn parse_maybe_signed(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| {
                if err.kind() == &IntErrorKind::PosOverflow && num_lit.negative {
                    IntErrorKind::NegOverflow
                } else {
                    err.kind().clone()
                }
            })
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

impl ParseMaybeSigned for u32 {
    fn parse_maybe_signed(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        Self::from_str_radix(num_lit.body, num_lit.radix)
            .map_err(|err| {
                if err.kind() == &IntErrorKind::PosOverflow && num_lit.negative {
                    IntErrorKind::NegOverflow
                } else {
                    err.kind().clone()
                }
            })
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

pub trait ParseSigned {
    fn parse_signed(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized;
}

impl ParseSigned for u16 {
    fn parse_signed(num_lit: NumLiteral) -> Result<Self, IntErrorKind>
    where
        Self: Sized,
    {
        i16::from_str_radix(num_lit.body, num_lit.radix)
            .map(|i| i as u16)
            .map_err(|err| {
                if err.kind() == &IntErrorKind::PosOverflow && num_lit.negative {
                    IntErrorKind::NegOverflow
                } else {
                    err.kind().clone()
                }
            })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Data<'a> {
    pub pos: usize,
    pub label: &'a str,
    pub decl: DataDeclaration<'a>,
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
    Num(NumLiteral<'a>),
    Char(char),
    String(&'a str),
    Ident(&'a str),
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

impl<'a> From<Token<'a>> for ParseError<'a> {
    fn from(t: Token<'a>) -> Self {
        ParseError {
            pos: t.pos,
            kind: ParseErrorKind::UnexpectedToken(t.kind),
        }
    }
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
                    Err(ParseError::from(t))
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
                    Err(ParseError::from(t))
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
                    Err(ParseError::from(t))
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
        while Some(&TokenKind::Whitespace) == $ti.peek().map(|t| &t.kind) {
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
                Err(ParseError::from(t))
            }
        }
    }};
}

macro_rules! impossible_whitespace {
    () => {{
        panic!("encountered whitespace after skipping whitespace");
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
                            pos: t.pos,
                            kind: ParseErrorKind::UnknownDirective(d),
                        })
                    }
                    TokenKind::Dot
                    | TokenKind::Comma
                    | TokenKind::Colon
                    | TokenKind::OpenParen
                    | TokenKind::CloseParen
                    | TokenKind::Dollar
                    | TokenKind::Whitespace
                    | TokenKind::Newline
                    | TokenKind::Literal(_) => return Err(ParseError::from(tn)),
                }
                let pos = skip_whitespace!(ti, tn.pos);
                expect!(ti, TokenKind::Newline, pos)?;
            }
            TokenKind::Ident(i) => {
                let s = match cs.as_mut() {
                    Some(s) => s,
                    None => {
                        // TODO: return something more helpful instructing the user to begin a section first
                        return Err(ParseError::from(t));
                    }
                };
                match &mut s.kind {
                    SectionKind::Data(data) => {
                        // It can only be a label
                        expect!(ti, TokenKind::Colon, t.pos)?;
                        let pos = skip_whitespace!(ti, t.pos + 1);
                        expect!(ti, TokenKind::Dot, pos)?;
                        let (kind_str, pos) = expect_ident!(ti, pos + 1)?;
                        let dot_pos = pos - 1;
                        let kind: DataKind =
                            DataKind::try_from(kind_str).map_err(|_| ParseError {
                                pos,
                                kind: ParseErrorKind::UnknownDataKind(kind_str),
                            })?;
                        let pos = skip_at_least_one_whitespace!(ti, pos)?;
                        let tn = ti.next().ok_or(ParseError {
                            pos,
                            kind: ParseErrorKind::UnexpectedEOF,
                        })?;
                        data.push(Data {
                            pos: t.pos,
                            label: i,
                            decl: DataDeclaration {
                                pos: dot_pos,
                                kind,
                                value_pos: tn.pos,
                                value: match tn.kind {
                                    TokenKind::Literal(Literal::Num(value)) => {
                                        skip_whitespace!(ti, tn.pos);
                                        match ti.next() {
                                            Some(t) => match t.kind {
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
                                                        Literal::Char(_) | Literal::Str(_) => {
                                                            return Err(ParseError {
                                                                pos: size_pos,
                                                                kind:
                                                                    ParseErrorKind::UnexpectedToken(
                                                                        TokenKind::Literal(
                                                                            size_lit,
                                                                        ),
                                                                    ),
                                                            });
                                                        }
                                                    }
                                                }
                                                TokenKind::Newline => DataValue::Num(value),
                                                TokenKind::Dot
                                                | TokenKind::Comma
                                                | TokenKind::OpenParen
                                                | TokenKind::CloseParen
                                                | TokenKind::Dollar
                                                | TokenKind::Ident(_)
                                                | TokenKind::Literal(_) => {
                                                    return Err(ParseError::from(t))
                                                }
                                                TokenKind::Whitespace => impossible_whitespace!(),
                                            },
                                            None => DataValue::Num(value),
                                        }
                                    }
                                    TokenKind::Literal(Literal::Char(c)) => DataValue::Char(c),
                                    TokenKind::Literal(Literal::Str(s)) => DataValue::String(s),
                                    TokenKind::Ident(s) => DataValue::Ident(s),
                                    TokenKind::Dot
                                    | TokenKind::Comma
                                    | TokenKind::Colon
                                    | TokenKind::OpenParen
                                    | TokenKind::CloseParen
                                    | TokenKind::Dollar
                                    | TokenKind::Newline => return Err(ParseError::from(tn)),
                                    TokenKind::Whitespace => impossible_whitespace!(),
                                },
                            },
                        })
                    }
                    SectionKind::Text(entries) => {
                        // We might get a label or an instruction

                        if Some(&TokenKind::Colon) == ti.peek().map(|t| &t.kind) {
                            // This is a label
                            ti.next().unreachable_unwrap();
                            entries.push(Entry {
                                pos: t.pos,
                                kind: EntryKind::Label(i),
                            })
                        } else {
                            // This is an instruction
                            let pos = t.pos;
                            let name = i;
                            let mut args = Vec::new();
                            let mut end_pos = skip_whitespace!(ti, t.pos + i.len());

                            let mut is_first = true;
                            loop {
                                let t = match ti.next() {
                                    Some(t) => t,
                                    None => {
                                        if is_first {
                                            break;
                                        } else {
                                            return Err(ParseError {
                                                pos: end_pos + 1,
                                                kind: ParseErrorKind::UnexpectedEOF,
                                            });
                                        }
                                    }
                                };
                                match t.kind {
                                    TokenKind::Newline => {
                                        if is_first {
                                            end_pos = t.pos;
                                            break;
                                        } else {
                                            return Err(ParseError::from(t));
                                        }
                                    }
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
                                            let Token { pos, .. } = ti.next().unreachable_unwrap();
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
                                    TokenKind::Dot
                                    | TokenKind::Comma
                                    | TokenKind::Colon
                                    | TokenKind::OpenParen
                                    | TokenKind::CloseParen
                                    | TokenKind::Literal(_) => return Err(ParseError::from(t)),
                                    TokenKind::Whitespace => impossible_whitespace!(),
                                }

                                end_pos = skip_whitespace!(ti, t.pos);
                                let t = match ti.next() {
                                    None => {
                                        end_pos += 1;
                                        break;
                                    }
                                    Some(t) => t,
                                };
                                match t.kind {
                                    TokenKind::Newline => {
                                        end_pos = t.pos;
                                        break;
                                    }
                                    TokenKind::Comma => {} // continue the loop and get the next arg
                                    TokenKind::Dot
                                    | TokenKind::Colon
                                    | TokenKind::OpenParen
                                    | TokenKind::CloseParen
                                    | TokenKind::Dollar
                                    | TokenKind::Ident(_)
                                    | TokenKind::Literal(_) => return Err(ParseError::from(t)),
                                    TokenKind::Whitespace => impossible_whitespace!(),
                                };

                                end_pos = skip_whitespace!(ti, t.pos);
                                is_first = false;
                            }

                            entries.push(Entry {
                                pos,
                                kind: EntryKind::Instruction(Instruction {
                                    name,
                                    args,
                                    end_pos,
                                }),
                            })
                        }
                    }
                };
            }
            TokenKind::Whitespace | TokenKind::Newline => {}
            TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::OpenParen
            | TokenKind::CloseParen
            | TokenKind::Dollar
            | TokenKind::Literal(_) => return Err(ParseError::from(t)),
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
    use crate::lex::LexErrorKind;
    use alloc::{borrow::ToOwned, format, vec};
    use pretty_assertions::assert_eq;

    macro_rules! parse_test {
        ($s:expr, $a:expr) => {
            assert_eq!(parse($s).unwrap(), $a)
        };
    }

    macro_rules! parse_err_test {
        ($s:expr, $e:expr) => {
            assert_eq!(parse($s).unwrap_err(), $e)
        };
    }

    macro_rules! parse_text_test {
        ($s:expr, $($e:expr),+ $(,)?) => {
            assert_eq!(parse(&(".text\n".to_owned() + $s)).unwrap().sections[0].kind, SectionKind::Text(vec![$($e),+]));
        };
    }

    macro_rules! parse_text_err_test {
        ($s:expr, $e:expr) => {
            parse_err_test!(&(".text\n".to_owned() + $s), $e)
        };
    }

    macro_rules! parse_data_test {
        ($s:expr, $($d:expr),+ $(,)?) => {
            assert_eq!(parse(&(".data\n".to_owned() + $s)).unwrap().sections[0].kind, SectionKind::Data(vec![$($d),+]));
        };
    }

    macro_rules! parse_data_err_test {
        ($s:expr, $e:expr) => {
            parse_err_test!(&(".data\n".to_owned() + $s), $e)
        };
    }

    macro_rules! token_kind_tuple {
        ($s:expr) => {
            ($s, lex($s).unwrap()[0].kind)
        };
    }

    macro_rules! token_kind_tuples {
        ($($s:expr),+ $(,)?) => {
            [$(token_kind_tuple!($s)),+]
        };
    }

    #[test]
    fn lex_error() {
        parse_text_err_test!(
            "!",
            ParseError {
                pos: 6,
                kind: ParseErrorKind::LexError(LexError {
                    pos: 6,
                    kind: LexErrorKind::UnexpectedToken('!')
                })
            }
        )
    }

    #[test]
    fn sections() {
        parse_test!(
            r#"
.data
.text
.text
.data
.data
            "#,
            Ast {
                sections: vec![
                    Section {
                        pos: 1,
                        kind: SectionKind::Data(vec![])
                    },
                    Section {
                        pos: 7,
                        kind: SectionKind::Text(vec![])
                    },
                    Section {
                        pos: 13,
                        kind: SectionKind::Text(vec![])
                    },
                    Section {
                        pos: 19,
                        kind: SectionKind::Data(vec![])
                    },
                    Section {
                        pos: 25,
                        kind: SectionKind::Data(vec![])
                    },
                ],
                eof_pos: 43
            }
        );
        parse_err_test!(
            ".asdf",
            ParseError {
                pos: 0,
                kind: ParseErrorKind::UnknownDirective("asdf")
            }
        );
        parse_err_test!(
            "..",
            ParseError {
                pos: 1,
                kind: ParseErrorKind::UnexpectedToken(TokenKind::Dot)
            }
        );
        parse_err_test!(
            ".data .data",
            ParseError {
                pos: 6,
                kind: ParseErrorKind::UnexpectedToken(TokenKind::Dot)
            }
        );
    }

    #[test]
    fn unexpected_main() {
        for (s, tk) in token_kind_tuples![",", ":", "(", ")", "$", "0", "a", "'a'", "\"a\""] {
            parse_err_test!(
                s,
                ParseError {
                    pos: 0,
                    kind: ParseErrorKind::UnexpectedToken(tk)
                }
            );
        }
    }

    #[test]
    fn data() {
        parse_data_test!(
            r#"
foo: .word 0
bar: .word 0 : 12
baz: .word "asdf"
__foo: .word foo
bar123: .hword 3
baz_foo: .hword 7 : 27
foo: .hword ""
bar: .half -7
baz: .half -8 : 37
__foo: .half "asdf\"asdf"
bar123: .byte 0x9f4e8a5
baz_foo: .byte 0b1101101 : -31
foo: .byte "\\"
bar: .byte 'a'
baz: .ascii 0o1673
__foo: .ascii -0o1673 : 0x615
bar123: .ascii "a string\n"
baz_foo: .asciiz -615456
foo: .asciiz "a\tstring"
bar: .word 0"#,
            Data {
                pos: 7,
                label: "foo",
                decl: DataDeclaration {
                    pos: 12,
                    kind: DataKind::Word,
                    value_pos: 18,
                    value: DataValue::Num(NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0",
                    }),
                },
            },
            Data {
                pos: 20,
                label: "bar",
                decl: DataDeclaration {
                    pos: 25,
                    kind: DataKind::Word,
                    value_pos: 31,
                    value: DataValue::Array {
                        value: NumLiteral {
                            negative: false,
                            radix: 10,
                            body: "0",
                        },
                        size_pos: 35,
                        size: NumLiteral {
                            negative: false,
                            radix: 10,
                            body: "12",
                        },
                    },
                },
            },
            Data {
                pos: 38,
                label: "baz",
                decl: DataDeclaration {
                    pos: 43,
                    kind: DataKind::Word,
                    value_pos: 49,
                    value: DataValue::String("asdf",),
                },
            },
            Data {
                pos: 56,
                label: "__foo",
                decl: DataDeclaration {
                    pos: 63,
                    kind: DataKind::Word,
                    value_pos: 69,
                    value: DataValue::Ident("foo",),
                },
            },
            Data {
                pos: 73,
                label: "bar123",
                decl: DataDeclaration {
                    pos: 81,
                    kind: DataKind::HalfWord,
                    value_pos: 88,
                    value: DataValue::Num(NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "3",
                    },),
                },
            },
            Data {
                pos: 90,
                label: "baz_foo",
                decl: DataDeclaration {
                    pos: 99,
                    kind: DataKind::HalfWord,
                    value_pos: 106,
                    value: DataValue::Array {
                        value: NumLiteral {
                            negative: false,
                            radix: 10,
                            body: "7",
                        },
                        size_pos: 110,
                        size: NumLiteral {
                            negative: false,
                            radix: 10,
                            body: "27",
                        },
                    },
                },
            },
            Data {
                pos: 113,
                label: "foo",
                decl: DataDeclaration {
                    pos: 118,
                    kind: DataKind::HalfWord,
                    value_pos: 125,
                    value: DataValue::String("",),
                },
            },
            Data {
                pos: 128,
                label: "bar",
                decl: DataDeclaration {
                    pos: 133,
                    kind: DataKind::HalfWord,
                    value_pos: 139,
                    value: DataValue::Num(NumLiteral {
                        negative: true,
                        radix: 10,
                        body: "7",
                    },),
                },
            },
            Data {
                pos: 142,
                label: "baz",
                decl: DataDeclaration {
                    pos: 147,
                    kind: DataKind::HalfWord,
                    value_pos: 153,
                    value: DataValue::Array {
                        value: NumLiteral {
                            negative: true,
                            radix: 10,
                            body: "8",
                        },
                        size_pos: 158,
                        size: NumLiteral {
                            negative: false,
                            radix: 10,
                            body: "37",
                        },
                    },
                },
            },
            Data {
                pos: 161,
                label: "__foo",
                decl: DataDeclaration {
                    pos: 168,
                    kind: DataKind::HalfWord,
                    value_pos: 174,
                    value: DataValue::String("asdf\\\"asdf",),
                },
            },
            Data {
                pos: 187,
                label: "bar123",
                decl: DataDeclaration {
                    pos: 195,
                    kind: DataKind::Byte,
                    value_pos: 201,
                    value: DataValue::Num(NumLiteral {
                        negative: false,
                        radix: 16,
                        body: "9f4e8a5",
                    },),
                },
            },
            Data {
                pos: 211,
                label: "baz_foo",
                decl: DataDeclaration {
                    pos: 220,
                    kind: DataKind::Byte,
                    value_pos: 226,
                    value: DataValue::Array {
                        value: NumLiteral {
                            negative: false,
                            radix: 2,
                            body: "1101101",
                        },
                        size_pos: 238,
                        size: NumLiteral {
                            negative: true,
                            radix: 10,
                            body: "31",
                        },
                    },
                },
            },
            Data {
                pos: 242,
                label: "foo",
                decl: DataDeclaration {
                    pos: 247,
                    kind: DataKind::Byte,
                    value_pos: 253,
                    value: DataValue::String("\\\\",),
                },
            },
            Data {
                pos: 258,
                label: "bar",
                decl: DataDeclaration {
                    pos: 263,
                    kind: DataKind::Byte,
                    value_pos: 269,
                    value: DataValue::Char('a',),
                },
            },
            Data {
                pos: 273,
                label: "baz",
                decl: DataDeclaration {
                    pos: 278,
                    kind: DataKind::Ascii,
                    value_pos: 285,
                    value: DataValue::Num(NumLiteral {
                        negative: false,
                        radix: 8,
                        body: "1673",
                    },),
                },
            },
            Data {
                pos: 292,
                label: "__foo",
                decl: DataDeclaration {
                    pos: 299,
                    kind: DataKind::Ascii,
                    value_pos: 306,
                    value: DataValue::Array {
                        value: NumLiteral {
                            negative: true,
                            radix: 8,
                            body: "1673",
                        },
                        size_pos: 316,
                        size: NumLiteral {
                            negative: false,
                            radix: 16,
                            body: "615",
                        },
                    },
                },
            },
            Data {
                pos: 322,
                label: "bar123",
                decl: DataDeclaration {
                    pos: 330,
                    kind: DataKind::Ascii,
                    value_pos: 337,
                    value: DataValue::String("a string\\n",),
                },
            },
            Data {
                pos: 350,
                label: "baz_foo",
                decl: DataDeclaration {
                    pos: 359,
                    kind: DataKind::Asciiz,
                    value_pos: 367,
                    value: DataValue::Num(NumLiteral {
                        negative: true,
                        radix: 10,
                        body: "615456",
                    },),
                },
            },
            Data {
                pos: 375,
                label: "foo",
                decl: DataDeclaration {
                    pos: 380,
                    kind: DataKind::Asciiz,
                    value_pos: 388,
                    value: DataValue::String("a\\tstring",),
                },
            },
            Data {
                pos: 400,
                label: "bar",
                decl: DataDeclaration {
                    pos: 405,
                    kind: DataKind::Word,
                    value_pos: 411,
                    value: DataValue::Num(NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0",
                    },),
                },
            },
        );
        parse_data_err_test!(
            "asdf: .asdfword 6",
            ParseError {
                pos: 13,
                kind: ParseErrorKind::UnknownDataKind("asdfword")
            }
        );
    }

    #[test]
    fn unexpected_data() {
        for (s, tk) in token_kind_tuples![".", ",", ":", "(", ")", "$", "\n"] {
            parse_data_err_test!(
                &("a: .word ".to_owned() + s),
                ParseError {
                    pos: 15,
                    kind: ParseErrorKind::UnexpectedToken(tk)
                }
            );
        }
        for (s, tk) in token_kind_tuples![".", ",", "(", ")", "$", "a", "'a'"] {
            parse_data_err_test!(
                &("a: .word 0".to_owned() + s),
                ParseError {
                    pos: 16,
                    kind: ParseErrorKind::UnexpectedToken(tk)
                }
            );
        }
        for (s, tk) in token_kind_tuples![".", ",", ":", "(", ")", "$", "\n", "a", "'a'", "\"a\""] {
            parse_data_err_test!(
                &("a: .word 0:".to_owned() + s),
                ParseError {
                    pos: 17,
                    kind: ParseErrorKind::UnexpectedToken(tk)
                }
            );
        }
    }

    #[test]
    fn text() {
        parse_text_test!(
            r#"
asdf: asdf $t0, 0, 0($t2), asdf
syscall
asdf 0"#,
            Entry {
                pos: 7,
                kind: EntryKind::Label("asdf"),
            },
            Entry {
                pos: 13,
                kind: EntryKind::Instruction(Instruction {
                    name: "asdf",
                    args: vec![
                        Argument {
                            pos: 18,
                            kind: ArgumentKind::Register("t0"),
                        },
                        Argument {
                            pos: 23,
                            kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                negative: false,
                                radix: 10,
                                body: "0",
                            })),
                        },
                        Argument {
                            pos: 26,
                            kind: ArgumentKind::OffsetRegister {
                                offset: NumLiteral {
                                    negative: false,
                                    radix: 10,
                                    body: "0",
                                },
                                register_pos: 28,
                                register: "t2",
                            },
                        },
                        Argument {
                            pos: 34,
                            kind: ArgumentKind::Label("asdf",),
                        },
                    ],
                    end_pos: 38,
                }),
            },
            Entry {
                pos: 39,
                kind: EntryKind::Instruction(Instruction {
                    name: "syscall",
                    args: vec![],
                    end_pos: 46,
                },),
            },
            Entry {
                pos: 47,
                kind: EntryKind::Instruction(Instruction {
                    name: "asdf",
                    args: vec![Argument {
                        pos: 52,
                        kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                            negative: false,
                            radix: 10,
                            body: "0",
                        })),
                    }],
                    end_pos: 53,
                }),
            },
        );
        parse_text_test!(
            "syscall",
            Entry {
                pos: 6,
                kind: EntryKind::Instruction(Instruction {
                    name: "syscall",
                    args: vec![],
                    end_pos: 13
                })
            }
        );
        parse_text_err_test!(
            "asdf $t0,",
            ParseError {
                pos: 15,
                kind: ParseErrorKind::UnexpectedEOF
            }
        );
        parse_text_err_test!(
            "asdf $t0,\n",
            ParseError {
                pos: 15,
                kind: ParseErrorKind::UnexpectedToken(TokenKind::Newline)
            }
        );
    }

    #[test]
    fn unexpected_argument() {
        for (s, tk) in token_kind_tuples![".", ",", ":", "(", ")", "'a'", "\"a\""] {
            parse_text_err_test!(
                &("a ".to_owned() + s),
                ParseError {
                    pos: 8,
                    kind: ParseErrorKind::UnexpectedToken(tk)
                }
            );
        }
        for (s, tk) in token_kind_tuples![".", ":", "(", ")", "'a'", "\"a\""] {
            parse_text_err_test!(
                &("a a ".to_owned() + s),
                ParseError {
                    pos: 10,
                    kind: ParseErrorKind::UnexpectedToken(tk)
                }
            );
        }
    }

    macro_rules! parse_unsigned_tests {
        ($t:ty) => {
            assert_eq!(
                <$t>::parse_unsigned(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: "9"
                })
                .unwrap(),
                9
            );
            assert_eq!(
                <$t>::parse_unsigned(NumLiteral {
                    negative: true,
                    radix: 10,
                    body: "9"
                })
                .unwrap_err(),
                IntErrorKind::NegOverflow
            );
            assert_eq!(
                <$t>::parse_unsigned(NumLiteral {
                    negative: false,
                    radix: 2,
                    body: "010010110"
                })
                .unwrap(),
                150
            );
            assert_eq!(
                <$t>::parse_unsigned(NumLiteral {
                    negative: false,
                    radix: 36,
                    body: "10000000000000000000000000000000000000000000000000000"
                })
                .unwrap_err(),
                IntErrorKind::PosOverflow
            );
        };
    }

    #[test]
    fn parse_unsigned() {
        parse_unsigned_tests!(u8);
        parse_unsigned_tests!(usize);
    }

    macro_rules! parse_maybe_signed_tests {
        ($t:ty, $ts:ty) => {
            assert_eq!(
                <$t>::parse_maybe_signed(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: &format!("{}", <$t>::MAX),
                })
                .unwrap(),
                <$t>::MAX
            );
            assert_eq!(
                <$t>::parse_maybe_signed(NumLiteral {
                    negative: true,
                    radix: 10,
                    body: &format!("{}", -(<$ts>::MIN + 1)),
                })
                .unwrap(),
                (<$ts>::MIN + 1) as $t
            );
            assert_eq!(
                <$t>::parse_maybe_signed(NumLiteral {
                    negative: false,
                    radix: 2,
                    body: "010010110"
                })
                .unwrap(),
                150
            );
            assert_eq!(
                <$t>::parse_maybe_signed(NumLiteral {
                    negative: false,
                    radix: 36,
                    body: "10000000000000000000000000000000000000000000000000000"
                })
                .unwrap_err(),
                IntErrorKind::PosOverflow
            );
            assert_eq!(
                <$t>::parse_maybe_signed(NumLiteral {
                    negative: true,
                    radix: 36,
                    body: "10000000000000000000000000000000000000000000000000000"
                })
                .unwrap_err(),
                IntErrorKind::NegOverflow
            );
        };
    }

    #[test]
    fn parse_maybe_signed() {
        parse_maybe_signed_tests!(u8, i8);
        parse_maybe_signed_tests!(u16, i16);
        parse_maybe_signed_tests!(u32, i32);
    }

    #[test]
    fn parse_signed() {
        assert_eq!(
            u16::parse_signed(NumLiteral {
                negative: false,
                radix: 10,
                body: "9"
            })
            .unwrap(),
            9
        );
        assert_eq!(
            u16::parse_signed(NumLiteral {
                negative: false,
                radix: 2,
                body: "010010110"
            })
            .unwrap(),
            150
        );
        assert_eq!(
            u16::parse_signed(NumLiteral {
                negative: false,
                radix: 10,
                body: &format!("{}", i16::MAX as i32 + 1),
            })
            .unwrap_err(),
            IntErrorKind::PosOverflow,
        );
        assert_eq!(
            u16::parse_signed(NumLiteral {
                negative: false,
                radix: 36,
                body: "10000000000000000000000000000000000000000000000000000"
            })
            .unwrap_err(),
            IntErrorKind::PosOverflow
        );
        assert_eq!(
            u16::parse_signed(NumLiteral {
                negative: true,
                radix: 36,
                body: "10000000000000000000000000000000000000000000000000000"
            })
            .unwrap_err(),
            IntErrorKind::NegOverflow
        );
    }

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
                                decl: DataDeclaration {
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
                                decl: DataDeclaration {
                                    pos: 222,
                                    kind: DataKind::Word,
                                    value_pos: 229,
                                    value: DataValue::Num(NumLiteral {
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
                                decl: DataDeclaration {
                                    pos: 1426,
                                    kind: DataKind::Asciiz,
                                    value_pos: 1435,
                                    value: DataValue::String(" ")
                                }
                            },
                            Data {
                                pos: 1482,
                                label: "head",
                                decl: DataDeclaration {
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

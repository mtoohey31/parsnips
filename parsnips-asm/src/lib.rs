#![no_std]

use parsnips_parser::{
    ArgumentKind, Ast, DataDeclaration, DataKind, DataValue, EntryKind, Instruction, Literal,
    NumLiteral, ParseMaybeSigned, ParseSigned, ParseUnsigned, SectionKind,
};
use parsnips_util::{Funct, Inst, Op};

extern crate alloc;
use alloc::{string::String, vec::Vec};
use ascii::{AsAsciiStr, AsAsciiStrError};
use core::{mem::size_of, num::IntErrorKind};
use hashbrown::HashMap;
use strum_macros::EnumString;

#[derive(Debug, PartialEq, EnumString)]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
enum Reg {
    Zero = 0,
    At = 1,
    V0 = 2,
    V1 = 3,
    A0 = 4,
    A1 = 5,
    A2 = 6,
    A3 = 7,
    T0 = 8,
    T1 = 9,
    T2 = 10,
    T3 = 11,
    T4 = 12,
    T5 = 13,
    T6 = 14,
    T7 = 15,
    S0 = 16,
    S1 = 17,
    S2 = 18,
    S3 = 19,
    S4 = 20,
    S5 = 21,
    S6 = 22,
    S7 = 23,
    T8 = 24,
    T9 = 25,
    K0 = 26,
    K1 = 27,
    Gp = 28,
    Sp = 29,
    Fp = 30,
    Ra = 31,
}

#[inline(always)]
fn new_reg(rs: Reg, rt: Reg, rd: Reg, shamt: u8, funct: Funct) -> Inst {
    ((Op::REG as u32) << 26)
        | ((rs as u32) << 21)
        | ((rt as u32) << 16)
        | ((rd as u32) << 11)
        | ((shamt as u32) << 6)
        | (funct as u32)
}

#[inline(always)]
fn new_arith_log_i(op: Op, rs: Reg, rt: Reg, imm: u16) -> Inst {
    ((op as u32) << 26) | ((rs as u32) << 21) | ((rt as u32) << 16) | (imm as u32)
}

#[inline(always)]
fn new_load_i(op: Op, rt: Reg, imm: u16) -> Inst {
    ((op as u32) << 26) | ((rt as u32) << 16) | (imm as u32)
}

#[inline(always)]
fn new_branch(op: Op, rs: Reg, rt: Reg) -> Inst {
    ((op as u32) << 26) | ((rs as u32) << 21) | ((rt as u32) << 16)
}

#[inline(always)]
fn new_branch_z(op: Op, rs: Reg) -> Inst {
    ((op as u32) << 26) | ((rs as u32) << 21)
}

#[inline(always)]
fn new_load_store(op: Op, rs: Reg, rt: Reg, imm: u16) -> Inst {
    ((op as u32) << 26) | ((rs as u32) << 21) | ((rt as u32) << 16) | (imm as u32)
}

#[inline(always)]
fn new_jump(op: Op) -> Inst {
    (op as u32) << 26
}

#[derive(Debug, PartialEq, Eq)]
pub struct AssembleError<'a> {
    pub pos: usize,
    kind: AssembleErrorKind<'a>,
}

impl<'a> From<DataDeclaration<'a>> for AssembleError<'a> {
    fn from(value: DataDeclaration<'a>) -> Self {
        AssembleError {
            pos: value.value_pos,
            kind: AssembleErrorKind::IllegalDataKindValueCombination(value.kind, value.value),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AssembleErrorKind<'a> {
    ExpectedArgument,
    InvalidArgument(ArgumentKind<'a>),
    InvalidDestination,
    MisalignedOffset(u16),
    NoText,
    InvalidStrEscape(char),
    IllegalDataKindValueCombination(DataKind, DataValue<'a>),
    NonAsciiChar(char),
    NonAsciiStr(AsAsciiStrError),
    OverflowingShamt(NumLiteral<'a>),
    OverflowingLabelReference(u32),
    ParseIntError(IntErrorKind),
    RedeclaredLabel(&'a str),
    UnexpectedArgument(ArgumentKind<'a>),
    UndefinedLabel(&'a str),
    UnknownInstruction(&'a str),
    UnknownReg(&'a str),
}

macro_rules! assert_nargs {
    ($args:expr, $n:expr, $end:expr) => {{
        if $args.len() < $n {
            return Err(AssembleError {
                pos: $end,
                kind: AssembleErrorKind::ExpectedArgument,
            });
        } else if $n < $args.len() {
            let a = $args.remove($n);
            return Err(AssembleError {
                pos: a.pos,
                kind: AssembleErrorKind::UnexpectedArgument(a.kind),
            });
        }
    }};
}

macro_rules! expect_reg {
    ($args:expr) => {{
        let a = $args.remove(0);
        if let ArgumentKind::Register(name) = a.kind {
            Ok((
                Reg::try_from(name).map_err(|_| AssembleError {
                    pos: a.pos,
                    kind: AssembleErrorKind::UnknownReg(name),
                })?,
                a.pos,
            ))
        } else {
            Err(AssembleError {
                pos: a.pos,
                kind: AssembleErrorKind::InvalidArgument(a.kind),
            })
        }?
    }};
}

macro_rules! expect_num_lit {
    ($args:expr) => {{
        let a = $args.remove(0);
        if let ArgumentKind::Literal(Literal::Num(lit)) = a.kind {
            Ok((lit, a.pos))
        } else {
            Err(AssembleError {
                pos: a.pos,
                kind: AssembleErrorKind::InvalidArgument(a.kind),
            })
        }?
    }};
}

#[inline(always)]
fn pad_len(len: usize) -> usize {
    let pad_len = 4 - len % 4;
    if pad_len == 4 {
        0
    } else {
        pad_len
    }
}

#[inline(always)]
fn pad(prog: &mut Vec<u8>, pad_len: usize) {
    for _ in 0..pad_len {
        prog.push(0);
    }
}

macro_rules! expect_label {
    ($args:expr) => {{
        let a = $args.remove(0);
        if let ArgumentKind::Label(lit) = a.kind {
            Ok((lit, a.pos))
        } else {
            Err(AssembleError {
                pos: a.pos,
                kind: AssembleErrorKind::InvalidArgument(a.kind),
            })
        }?
    }};
}

macro_rules! push_int {
    ($prog:expr, $value_ty:ty, $value_pos:expr, $value:expr) => {{
        let len = size_of::<$value_ty>();
        let pad_len = pad_len(len);
        $prog.reserve(len + pad_len);
        $prog.extend_from_slice(
            &<$value_ty>::parse_maybe_signed($value)
                .map_err(|e| AssembleError {
                    pos: $value_pos,
                    kind: AssembleErrorKind::ParseIntError(e),
                })?
                .to_le_bytes(),
        );
        pad(&mut $prog, pad_len);
    }};
}

macro_rules! push_array {
    ($prog:expr, $value_ty:ty, $value_pos:expr, $value:expr, $size_pos:expr, $size:expr) => {{
        let value = <$value_ty>::parse_maybe_signed($value).map_err(|e| AssembleError {
            pos: $value_pos,
            kind: AssembleErrorKind::ParseIntError(e),
        })?;
        let size = usize::parse_unsigned($size).map_err(|e| AssembleError {
            pos: $size_pos,
            kind: AssembleErrorKind::ParseIntError(e),
        })?;
        let len = size_of::<$value_ty>() * size;
        let pad_len = pad_len(len);
        $prog.reserve(len + pad_len);
        let value_bytes = value.to_le_bytes();
        for _ in 0..size {
            $prog.extend_from_slice(&value_bytes);
        }
        pad(&mut $prog, pad_len);
    }};
}

#[inline(always)]
fn unescape(s: &str, start_pos: usize) -> Result<String, AssembleError> {
    let mut unescaped = String::new();
    let mut ci = s.chars().enumerate();
    while let Some((bslsh_pos, c)) = ci.next() {
        unescaped.push(match c {
            '\\' => match ci.next() {
                Some((_, 't')) => '\t',
                Some((_, 'n')) => '\n',
                Some((_, '\\')) => '\\',
                Some((invalid_pos, c)) => {
                    return Err(AssembleError {
                        pos: start_pos + invalid_pos,
                        kind: AssembleErrorKind::InvalidStrEscape(c),
                    })
                }
                None => {
                    // this error maybe isn't really the most
                    // appropriate thing for this case, but this error
                    // case shouldn't occur with a well-formed AST
                    // produced by lex and parse anyways so...
                    return Err(AssembleError {
                        pos: start_pos + bslsh_pos + 1,
                        kind: AssembleErrorKind::InvalidStrEscape(c),
                    });
                }
            },
            o => o,
        })
    }

    Ok(unescaped)
}

const SYSCALL: Inst = (Op::SYSCALL as u32) << 26;

#[derive(Debug)]
struct LabelReference<'a> {
    ident: &'a str,
    // the byte index within the program
    location: usize,
    // the character index within the source code
    pos: usize,
    kind: ReferenceKind,
}

#[derive(Debug)]
enum ReferenceKind {
    // |= addr >> 2 asserting bitwidth is <= 26
    Jump,
    // |= (addr - (current + 4)) >> 2 asserting bitwidth is <= 16
    Imm,
    // |= addr asserting bitwidth is <= 16
    RawImm,
    // |= addr
    Raw,
}

pub fn assemble(ast: Ast) -> Result<Vec<u8>, AssembleError> {
    let mut program = Vec::new();
    let mut label_definitions = HashMap::new();
    let mut label_references = Vec::new();
    let mut initial_section_data: Option<bool> = None;
    // an optional tuple of u32 byte index within the program and usize character index within the source code
    let mut initial_text_section: Option<(u32, usize)> = None;

    for section in ast.sections {
        match section.kind {
            SectionKind::Data(entries) => {
                if initial_section_data.is_none() {
                    initial_section_data = Some(true);
                    program.extend_from_slice(&new_jump(Op::J).to_le_bytes());
                }

                for entry in entries {
                    label_definitions.insert(entry.label, program.len());
                    match entry.decl.kind {
                        DataKind::Word => match entry.decl.value {
                            DataValue::Num(value) => {
                                push_int!(program, u32, entry.decl.pos, value);
                            }
                            DataValue::Array {
                                value,
                                size_pos,
                                size,
                            } => {
                                push_array!(program, u32, entry.decl.pos, value, size_pos, size);
                            }
                            DataValue::Ident(ident) => {
                                label_references.push(LabelReference {
                                    ident,
                                    location: program.len(),
                                    pos: entry.decl.value_pos,
                                    kind: ReferenceKind::Raw,
                                });
                                pad(&mut program, 4);
                            }
                            DataValue::Char(_) | DataValue::String(_) => {
                                return Err(AssembleError::from(entry.decl))
                            }
                        },
                        DataKind::HalfWord => match entry.decl.value {
                            DataValue::Num(value) => {
                                push_int!(program, u16, entry.decl.pos, value);
                            }
                            DataValue::Array {
                                value,
                                size_pos,
                                size,
                            } => {
                                push_array!(program, u16, entry.decl.pos, value, size_pos, size);
                            }
                            DataValue::Char(_) | DataValue::String(_) | DataValue::Ident(_) => {
                                return Err(AssembleError::from(entry.decl))
                            }
                        },
                        DataKind::Byte => match entry.decl.value {
                            DataValue::Num(value) => {
                                push_int!(program, u8, entry.decl.pos, value);
                            }
                            DataValue::Array {
                                value,
                                size_pos,
                                size,
                            } => {
                                push_array!(program, u8, entry.decl.pos, value, size_pos, size);
                            }
                            DataValue::Char(c) => {
                                if !c.is_ascii() {
                                    return Err(AssembleError {
                                        pos: entry.decl.value_pos + 1,
                                        kind: AssembleErrorKind::NonAsciiChar(c),
                                    });
                                }
                                program.reserve(4);
                                program.push(c as u8);
                                pad(&mut program, 3);
                            }
                            DataValue::String(_) | DataValue::Ident(_) => {
                                return Err(AssembleError::from(entry.decl))
                            }
                        },
                        DataKind::Ascii => match entry.decl.value {
                            DataValue::String(s) => {
                                let unescaped = unescape(s, entry.decl.value_pos + 1)?;
                                let ascii_str =
                                    unescaped.as_ascii_str().map_err(|e| AssembleError {
                                        pos: entry.decl.value_pos + 1 + e.valid_up_to(),
                                        kind: AssembleErrorKind::NonAsciiStr(e),
                                    })?;
                                let bytes = ascii_str.as_bytes();
                                let pad_len = pad_len(bytes.len());
                                program.reserve(bytes.len() + pad_len);
                                program.extend_from_slice(bytes);
                                pad(&mut program, pad_len);
                            }
                            DataValue::Num(_)
                            | DataValue::Char(_)
                            | DataValue::Ident(_)
                            | DataValue::Array { .. } => {
                                return Err(AssembleError::from(entry.decl))
                            }
                        },
                        DataKind::Asciiz => match entry.decl.value {
                            DataValue::String(s) => {
                                let unescaped = unescape(s, entry.decl.value_pos + 1)?;
                                let ascii_str =
                                    unescaped.as_ascii_str().map_err(|e| AssembleError {
                                        pos: entry.decl.value_pos + 1 + e.valid_up_to(),
                                        kind: AssembleErrorKind::NonAsciiStr(e),
                                    })?;
                                let bytes = ascii_str.as_bytes();
                                // account for the required zero byte
                                let pad_len = pad_len(bytes.len() + 1);
                                program.reserve(bytes.len() + 1 + pad_len);
                                program.extend_from_slice(bytes);
                                pad(&mut program, pad_len + 1);
                            }
                            DataValue::Num(_)
                            | DataValue::Char(_)
                            | DataValue::Ident(_)
                            | DataValue::Array { .. } => {
                                return Err(AssembleError::from(entry.decl))
                            }
                        },
                    }
                }
            }
            SectionKind::Text(entries) => {
                if initial_section_data.is_none() {
                    initial_section_data = Some(false);
                }
                if initial_text_section.is_none() {
                    initial_text_section = Some((program.len() as u32, section.pos));
                }

                for entry in entries {
                    match entry.kind {
                        EntryKind::Label(name) => {
                            if label_definitions.insert(name, program.len()).is_some() {
                                return Err(AssembleError {
                                    pos: entry.pos,
                                    kind: AssembleErrorKind::RedeclaredLabel(name),
                                });
                            }
                        }
                        EntryKind::Instruction(Instruction {
                            name,
                            args: mut arguments,
                            end_pos,
                        }) => {
                            if let Ok(op) = Op::try_from(name) {
                                let inst = match op {
                                    Op::ADDI
                                    | Op::ADDIU
                                    | Op::ANDI
                                    | Op::ORI
                                    | Op::XORI
                                    | Op::SLTI
                                    | Op::SLTIU => {
                                        assert_nargs!(arguments, 3, end_pos);
                                        let (reg, pos) = expect_reg!(arguments);
                                        match reg {
                                            Reg::Zero => {
                                                return Err(AssembleError {
                                                    pos,
                                                    kind: AssembleErrorKind::InvalidDestination,
                                                })
                                            }
                                            rt => {
                                                let rs = expect_reg!(arguments).0;
                                                let (lit, pos) = expect_num_lit!(arguments);
                                                new_arith_log_i(
                                                    op,
                                                    rs,
                                                    rt,
                                                    u16::parse_maybe_signed(lit).map_err(|e| {
                                                        AssembleError {
                                                            pos,
                                                            kind: AssembleErrorKind::ParseIntError(
                                                                e,
                                                            ),
                                                        }
                                                    })?,
                                                )
                                            }
                                        }
                                    }

                                    Op::LHI | Op::LLO => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let (reg, pos) = expect_reg!(arguments);
                                        let (lit, lit_pos) = expect_num_lit!(arguments);
                                        match reg {
                                            Reg::Zero => {
                                                return Err(AssembleError {
                                                    pos,
                                                    kind: AssembleErrorKind::InvalidDestination,
                                                });
                                            }
                                            rt => new_load_i(
                                                op,
                                                rt,
                                                u16::parse_maybe_signed(lit).map_err(|e| {
                                                    AssembleError {
                                                        pos: lit_pos,
                                                        kind: AssembleErrorKind::ParseIntError(e),
                                                    }
                                                })?,
                                            ),
                                        }
                                    }

                                    Op::BEQ | Op::BNE => {
                                        assert_nargs!(arguments, 3, end_pos);
                                        let (rs, rt) =
                                            (expect_reg!(arguments).0, expect_reg!(arguments).0);
                                        let (ident, pos) = expect_label!(arguments);
                                        label_references.push(LabelReference {
                                            ident,
                                            location: program.len(),
                                            pos,
                                            kind: ReferenceKind::Imm,
                                        });
                                        new_branch(op, rs, rt)
                                    }

                                    Op::BGTZ | Op::BLEZ => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let rs = expect_reg!(arguments).0;
                                        let (ident, pos) = expect_label!(arguments);
                                        label_references.push(LabelReference {
                                            ident,
                                            location: program.len(),
                                            pos,
                                            kind: ReferenceKind::Imm,
                                        });
                                        new_branch_z(op, rs)
                                    }

                                    Op::LB | Op::LBU | Op::SB => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let rt = expect_reg!(arguments).0;
                                        let a = arguments.remove(0);
                                        if let ArgumentKind::OffsetRegister {
                                            offset,
                                            register,
                                            register_pos,
                                        } = a.kind
                                        {
                                            new_load_store(
                                                op,
                                                Reg::try_from(register).map_err(|_| {
                                                    AssembleError {
                                                        pos: register_pos,
                                                        kind: AssembleErrorKind::UnknownReg(
                                                            register,
                                                        ),
                                                    }
                                                })?,
                                                rt,
                                                u16::parse_signed(offset).map_err(|e| {
                                                    AssembleError {
                                                        pos: a.pos,
                                                        kind: AssembleErrorKind::ParseIntError(e),
                                                    }
                                                })?,
                                            )
                                        } else {
                                            return Err(AssembleError {
                                                pos: a.pos,
                                                kind: AssembleErrorKind::UnexpectedArgument(a.kind),
                                            });
                                        }
                                    }

                                    Op::LH | Op::LHU | Op::SH => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let rt = expect_reg!(arguments).0;
                                        let a = arguments.remove(0);
                                        if let ArgumentKind::OffsetRegister {
                                            offset,
                                            register,
                                            register_pos,
                                        } = a.kind
                                        {
                                            let offset =
                                                u16::parse_signed(offset).map_err(|e| {
                                                    AssembleError {
                                                        pos: a.pos,
                                                        kind: AssembleErrorKind::ParseIntError(e),
                                                    }
                                                })?;
                                            if offset % 2 != 0 {
                                                return Err(AssembleError {
                                                    pos: a.pos,
                                                    kind: AssembleErrorKind::MisalignedOffset(
                                                        offset,
                                                    ),
                                                });
                                            }

                                            new_load_store(
                                                op,
                                                Reg::try_from(register).map_err(|_| {
                                                    AssembleError {
                                                        pos: register_pos,
                                                        kind: AssembleErrorKind::UnknownReg(
                                                            register,
                                                        ),
                                                    }
                                                })?,
                                                rt,
                                                offset,
                                            )
                                        } else {
                                            return Err(AssembleError {
                                                pos: a.pos,
                                                kind: AssembleErrorKind::UnexpectedArgument(a.kind),
                                            });
                                        }
                                    }

                                    Op::LW | Op::SW => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let rt = expect_reg!(arguments).0;
                                        let a = arguments.remove(0);
                                        if let ArgumentKind::OffsetRegister {
                                            offset,
                                            register,
                                            register_pos,
                                        } = a.kind
                                        {
                                            let offset =
                                                u16::parse_signed(offset).map_err(|e| {
                                                    AssembleError {
                                                        pos: a.pos,
                                                        kind: AssembleErrorKind::ParseIntError(e),
                                                    }
                                                })?;
                                            if offset % 4 != 0 {
                                                return Err(AssembleError {
                                                    pos: a.pos,
                                                    kind: AssembleErrorKind::MisalignedOffset(
                                                        offset,
                                                    ),
                                                });
                                            }

                                            new_load_store(
                                                op,
                                                Reg::try_from(register).map_err(|_| {
                                                    AssembleError {
                                                        pos: register_pos,
                                                        kind: AssembleErrorKind::UnknownReg(
                                                            register,
                                                        ),
                                                    }
                                                })?,
                                                rt,
                                                offset,
                                            )
                                        } else {
                                            return Err(AssembleError {
                                                pos: a.pos,
                                                kind: AssembleErrorKind::UnexpectedArgument(a.kind),
                                            });
                                        }
                                    }

                                    Op::J | Op::JAL => {
                                        assert_nargs!(arguments, 1, end_pos);
                                        let (ident, pos) = expect_label!(arguments);
                                        label_references.push(LabelReference {
                                            ident,
                                            location: program.len(),
                                            pos,
                                            kind: ReferenceKind::Jump,
                                        });
                                        new_jump(op)
                                    }

                                    Op::SYSCALL => {
                                        if arguments.len() > 0 {
                                            let a = arguments.remove(0);
                                            return Err(AssembleError {
                                                pos: a.pos,
                                                kind: AssembleErrorKind::UnexpectedArgument(a.kind),
                                            });
                                        }

                                        SYSCALL
                                    }

                                    Op::REG => {
                                        return Err(AssembleError {
                                            pos: entry.pos,
                                            kind: AssembleErrorKind::UnknownInstruction(name),
                                        })
                                    }
                                };

                                program.extend_from_slice(&inst.to_le_bytes());
                            } else if let Ok(funct) = Funct::try_from(name) {
                                let (mut rs, mut rt) = (Reg::Zero, Reg::Zero);
                                let mut rd = None;
                                let mut shamt = 0;

                                match funct {
                                    Funct::ADD
                                    | Funct::ADDU
                                    | Funct::AND
                                    | Funct::NOR
                                    | Funct::OR
                                    | Funct::SUB
                                    | Funct::SUBU
                                    | Funct::XOR
                                    | Funct::SLT
                                    | Funct::SLTU => {
                                        assert_nargs!(arguments, 3, end_pos);
                                        rd = Some(expect_reg!(arguments));
                                        rs = expect_reg!(arguments).0;
                                        rt = expect_reg!(arguments).0;
                                    }

                                    Funct::MULT | Funct::MULTU | Funct::DIV | Funct::DIVU => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        rs = expect_reg!(arguments).0;
                                        rt = expect_reg!(arguments).0;
                                    }

                                    Funct::SLL | Funct::SRL | Funct::SRA => {
                                        assert_nargs!(arguments, 3, end_pos);
                                        rd = Some(expect_reg!(arguments));
                                        rt = expect_reg!(arguments).0;
                                        let (shamt_lit, lit_pos) = expect_num_lit!(arguments);
                                        match u8::parse_unsigned(shamt_lit.clone()) {
                                            Ok(s) => {
                                                shamt = s;
                                                if shamt > 16 {
                                                    return Err(AssembleError {
                                                        pos: lit_pos,
                                                        kind: AssembleErrorKind::OverflowingShamt(
                                                            shamt_lit,
                                                        ),
                                                    });
                                                };
                                            }
                                            Err(e) => {
                                                return Err(AssembleError {
                                                    pos: lit_pos,
                                                    kind: match e {
                                                        IntErrorKind::PosOverflow
                                                        | IntErrorKind::NegOverflow => {
                                                            AssembleErrorKind::OverflowingShamt(
                                                                shamt_lit,
                                                            )
                                                        }
                                                        _ => AssembleErrorKind::ParseIntError(e),
                                                    },
                                                });
                                            }
                                        };
                                    }

                                    Funct::SLLV | Funct::SRLV | Funct::SRAV => {
                                        assert_nargs!(arguments, 3, end_pos);
                                        rd = Some(expect_reg!(arguments));
                                        rt = expect_reg!(arguments).0;
                                        rs = expect_reg!(arguments).0;
                                    }

                                    Funct::JR | Funct::JALR => {
                                        assert_nargs!(arguments, 1, end_pos);
                                        rs = expect_reg!(arguments).0;
                                    }

                                    Funct::MFHI | Funct::MFLO => {
                                        assert_nargs!(arguments, 1, end_pos);
                                        rd = Some(expect_reg!(arguments));
                                    }

                                    Funct::MTHI | Funct::MTLO => {
                                        assert_nargs!(arguments, 1, end_pos);
                                        rs = expect_reg!(arguments).0;
                                    }
                                }

                                // If rd was explicitly set to zero that means it will actually be
                                // used as a destination, which is illegal. If it's unset, then we
                                // will use zero as the default since its primitive representation
                                // is 0. It won't actually be used during runtime in this case, so
                                // it could be set to anything, but we should make it zero to avoid
                                // confusion.
                                if let Some((Reg::Zero, pos)) = rd {
                                    return Err(AssembleError {
                                        pos,
                                        kind: AssembleErrorKind::InvalidDestination,
                                    });
                                }
                                program.extend_from_slice(
                                    &new_reg(
                                        rs,
                                        rt,
                                        rd.map(|(rd, _)| rd).unwrap_or(Reg::Zero),
                                        shamt,
                                        funct,
                                    )
                                    .to_le_bytes(),
                                );
                            } else {
                                // TODO: make pseudo-instructions configurable?
                                match name {
                                    "la" => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let rt = expect_reg!(arguments).0;
                                        let (ident, pos) = expect_label!(arguments);
                                        label_references.push(LabelReference {
                                            ident,
                                            location: program.len(),
                                            pos,
                                            kind: ReferenceKind::RawImm,
                                        });
                                        program.extend_from_slice(
                                            &new_arith_log_i(Op::ADDI, Reg::Zero, rt, 0)
                                                .to_le_bytes(),
                                        );
                                    }
                                    "li" => {
                                        assert_nargs!(arguments, 2, end_pos);
                                        let rt = expect_reg!(arguments).0;
                                        let (lit, pos) = expect_num_lit!(arguments);
                                        program.extend_from_slice(
                                            &new_arith_log_i(
                                                Op::ADDI,
                                                Reg::Zero,
                                                rt,
                                                u16::parse_maybe_signed(lit).map_err(|e| {
                                                    AssembleError {
                                                        pos,
                                                        kind: AssembleErrorKind::ParseIntError(e),
                                                    }
                                                })?,
                                            )
                                            .to_le_bytes(),
                                        );
                                    }
                                    _ => {
                                        return Err(AssembleError {
                                            pos: entry.pos,
                                            kind: AssembleErrorKind::UnknownInstruction(name),
                                        })
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    for reference in label_references {
        let definition = label_definitions
            .get(reference.ident)
            .ok_or_else(|| AssembleError {
                pos: reference.pos,
                kind: AssembleErrorKind::UndefinedLabel(reference.ident),
            })?;
        let imm: u32 = match reference.kind {
            ReferenceKind::Jump => {
                let full = (*definition as i32 - (reference.location + 4) as i32) >> 2;
                full.checked_shl(6)
                    .ok_or(AssembleErrorKind::OverflowingLabelReference(full as u32))
                    .map(|s| s as u32 >> 6)
            }
            ReferenceKind::Imm => {
                let full = (*definition as i32 - (reference.location + 4) as i32) >> 2;
                i16::try_from(full)
                    .map_err(|_| AssembleErrorKind::OverflowingLabelReference(full as u32))
                    .map(|s| s as u16 as u32)
            }
            ReferenceKind::RawImm => {
                let full = *definition as i32;
                i16::try_from(full)
                    .map_err(|_| AssembleErrorKind::OverflowingLabelReference(full as u32))
                    .map(|s| s as u16 as u32)
            }
            ReferenceKind::Raw => Ok(*definition as u32),
        }
        .map_err(|kind| AssembleError {
            pos: reference.pos,
            kind,
        })?;
        // TODO: remove all align_to's because these aren't guaranteed to do what we want; they
        // might have prefixes/suffixes
        unsafe { program[reference.location..].align_to_mut::<u32>() }.1[0] |= imm.to_le();
    }

    if Some(true) == initial_section_data {
        let (location, pos) = initial_text_section.ok_or(AssembleError {
            pos: ast.eof_pos,
            kind: AssembleErrorKind::NoText,
        })?;
        let imm = location - 4 >> 2;
        if imm > (1 << 26) - 1 {
            return Err(AssembleError {
                pos,
                kind: AssembleErrorKind::OverflowingLabelReference(imm),
            });
        }
        unsafe { program.align_to_mut::<u32>() }.1[0] |= imm;
    }

    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{borrow::ToOwned, format, vec};
    use parsnips_parser::{parse, Argument, Data, Entry, Section};
    use pretty_assertions::assert_eq;

    fn str_to_u32(input: &str) -> u32 {
        input
            .chars()
            .take(4)
            .fold(0, |acc, c| (acc >> 8) + ((c as u32) << 24))
    }

    macro_rules! program {
        ($($x:expr),+ $(,)?) => (
            unsafe { [$($x),+].map(u32::to_le).align_to::<u8>() }.1
        );
    }

    macro_rules! asm_test {
        ($s:expr,$($x:expr),+ $(,)?) => {
            assert_eq!(assemble(parse($s).unwrap()).unwrap(), program![$($x),+])
        }
    }

    macro_rules! asm_err_test {
        ($s:expr,$err:expr) => {
            assert_eq!(assemble(parse($s).unwrap()).unwrap_err(), $err)
        };
    }

    macro_rules! asm_text_test {
        ($s:expr,$($x:expr),+ $(,)?) => {
            asm_test!(&(".text\n".to_owned() + $s), $($x),+)
        }
    }

    macro_rules! asm_text_err_test {
        ($s:expr,$err:expr) => {
            asm_err_test!(&(".text\n".to_owned() + $s), $err)
        };
    }

    macro_rules! asm_data_test {
        ($s:expr,$($x:expr),+ $(,)?) => {
            asm_test!(&(".text\n.data\n".to_owned() + $s), $($x),+)
        }
    }

    macro_rules! asm_data_err_test {
        ($s:expr,$err:expr) => {
            asm_err_test!(&(".text\n.data\n".to_owned() + $s), $err)
        };
    }

    #[test]
    fn basic() {
        asm_test!(
            include_str!("../../test/basic.asm"),
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::T0, 13),
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::T1, 26),
            new_reg(Reg::T0, Reg::T1, Reg::T2, 0, Funct::ADD)
        );
    }

    #[test]
    fn fib() {
        let mut expected: Vec<u8> = Vec::new();
        expected.extend_from_slice(program![
            new_jump(Op::J) | 13, // assembler inserted jump to first .text
            // .data
            // fibs
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            // size
            12,
            // .text
            // la $t0, fibs
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::T0, 1 * 4),
            // la $t5, fibs
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::T5, 13 * 4),
            // lw $t5, 0($t5)
            new_load_store(Op::LW, Reg::T5, Reg::T5, 0),
            // li $t2, 1
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::T2, 1),
            // sw $t2, 0($t0)
            new_load_store(Op::SW, Reg::T0, Reg::T2, 0),
            // sw $t2, 4($t0)
            new_load_store(Op::SW, Reg::T0, Reg::T2, 4),
            // addi $t1, $t5, -2
            new_arith_log_i(Op::ADDI, Reg::T5, Reg::T1, -2 as i16 as u16),
            // loop: lw $t3, 0($t0)
            new_load_store(Op::LW, Reg::T0, Reg::T3, 0),
            // lw $t4, 4($t0)
            new_load_store(Op::LW, Reg::T0, Reg::T4, 4),
            // add $t2, $t3, $t4
            new_reg(Reg::T3, Reg::T4, Reg::T2, 0, Funct::ADD),
            // sw $t2, 8($t0)
            new_load_store(Op::SW, Reg::T0, Reg::T2, 8),
            // addi $t0, $t0, 4
            new_arith_log_i(Op::ADDI, Reg::T0, Reg::T0, 4),
            // addi $t1, $t1, -1
            new_arith_log_i(Op::ADDI, Reg::T1, Reg::T1, -1 as i16 as u16),
            // bgtz $t1, loop
            new_branch_z(Op::BGTZ, Reg::T1) | ((21 - (27 + 1)) as i16 as u16 as u32),
            // la $a0, fibs
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::A0, 1 * 4),
            // add $a1, $zero, $t5
            new_reg(Reg::Zero, Reg::T5, Reg::A1, 0, Funct::ADD),
            // jal print
            new_jump(Op::JAL) | 10,
            // li $v0, 10
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::V0, 10),
            // syscall
            SYSCALL,
            // .data
            // space:.asciiz " "
            str_to_u32(" \0\0\0"),
            // head: .asciiz "The Fibonacci numbers are:\n"
            str_to_u32("The "),
            str_to_u32("Fibo"),
            str_to_u32("nacc"),
            str_to_u32("i nu"),
            str_to_u32("mber"),
            str_to_u32("s ar"),
            str_to_u32("e:\n\0"),
        ]);
        expected.extend_from_slice(program![
            // .text
            // print: add $t0, $zero, $a0
            new_reg(Reg::Zero, Reg::A0, Reg::T0, 0, Funct::ADD),
            // add $t1, $zero, $a1
            new_reg(Reg::Zero, Reg::A1, Reg::T1, 0, Funct::ADD),
            // la $a0, head
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::A0, 34 * 4),
            // li $v0, 4
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::V0, 4),
            // syscall
            SYSCALL,
            // out: lw $a0, 0($t0)
            new_load_store(Op::LW, Reg::T0, Reg::A0, 0),
            // li $v0, 1
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::V0, 1),
            // syscall
            SYSCALL,
            // la $a0, space
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::A0, 33 * 4),
            // li $v0, 4
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::V0, 4),
            // syscall
            SYSCALL,
            // addi $t0, $t0, 4
            new_arith_log_i(Op::ADDI, Reg::T0, Reg::T0, 4),
            // addi $t1, $t1, -1
            new_arith_log_i(Op::ADDI, Reg::T1, Reg::T1, -1 as i16 as u16),
            // bgtz $t1, out
            new_branch_z(Op::BGTZ, Reg::T1) | (-9 as i16 as u16 as u32),
            // jr $ra
            new_reg(Reg::Ra, Reg::Zero, Reg::Zero, 0, Funct::JR),
        ]);
        assert_eq!(
            assemble(parse(include_str!("../../test/fib.asm")).unwrap()).unwrap(),
            expected
        );
    }

    #[test]
    fn register_names() {
        asm_text_test!(
            "add $v0, $zero, $v1",
            new_reg(Reg::Zero, Reg::V1, Reg::V0, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $a0, $a1, $a2",
            new_reg(Reg::A1, Reg::A2, Reg::A0, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $a3, $t0, $t1",
            new_reg(Reg::T0, Reg::T1, Reg::A3, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $t2, $t3, $t4",
            new_reg(Reg::T3, Reg::T4, Reg::T2, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $t5, $t6, $t7",
            new_reg(Reg::T6, Reg::T7, Reg::T5, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $s0, $s1, $s2",
            new_reg(Reg::S1, Reg::S2, Reg::S0, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $s3, $s4, $s5",
            new_reg(Reg::S4, Reg::S5, Reg::S3, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $s6, $s7, $t8",
            new_reg(Reg::S7, Reg::T8, Reg::S6, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $t9, $k0, $k1",
            new_reg(Reg::K0, Reg::K1, Reg::T9, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $gp, $sp, $fp",
            new_reg(Reg::Sp, Reg::Fp, Reg::Gp, 0, Funct::ADD)
        );
        asm_text_test!(
            "add $ra, $ra, $ra",
            new_reg(Reg::Ra, Reg::Ra, Reg::Ra, 0, Funct::ADD)
        );
    }

    #[test]
    fn invalid_dest() {
        asm_text_err_test!(
            "addi $zero, $zero, 0",
            AssembleError {
                pos: 11,
                kind: AssembleErrorKind::InvalidDestination
            }
        );
        asm_text_err_test!(
            "lhi $zero, 94",
            AssembleError {
                pos: 10,
                kind: AssembleErrorKind::InvalidDestination
            }
        );
        asm_text_err_test!(
            "add $zero, $zero, $zero",
            AssembleError {
                pos: 10,
                kind: AssembleErrorKind::InvalidDestination
            }
        );
    }

    #[test]
    fn unknown_instruction() {
        asm_text_err_test!(
            "reg $t0, $t0, $t0",
            AssembleError {
                pos: 6,
                kind: AssembleErrorKind::UnknownInstruction("reg")
            }
        );
        asm_text_err_test!(
            "bogus $t0, $t0, $t0",
            AssembleError {
                pos: 6,
                kind: AssembleErrorKind::UnknownInstruction("bogus")
            }
        );
        // identifiers are case sensitive
        asm_text_err_test!(
            "ADD $t0, $t0, $t0",
            AssembleError {
                pos: 6,
                kind: AssembleErrorKind::UnknownInstruction("ADD")
            }
        );
    }

    #[test]
    fn redeclared_label() {
        asm_text_err_test!(
            r#"
EXIT:
EXIT:
            "#,
            AssembleError {
                pos: 13,
                kind: AssembleErrorKind::RedeclaredLabel("EXIT")
            }
        );
        asm_text_err_test!(
            r#"
EXIT:
    .text
EXIT:
            "#,
            AssembleError {
                pos: 23,
                kind: AssembleErrorKind::RedeclaredLabel("EXIT")
            }
        );
    }

    #[test]
    fn misaligned_offset() {
        asm_text_err_test!(
            "lh $t0, 1($t1)",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::MisalignedOffset(1)
            }
        );
        asm_text_err_test!(
            "lw $t0, 2($t1)",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::MisalignedOffset(2)
            }
        );
    }

    #[test]
    fn unexpected_arg() {
        asm_text_err_test!(
            "addi $t0, $zero, 4, 9",
            AssembleError {
                pos: 26,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "9"
                    }
                )))
            }
        );
        asm_text_err_test!(
            "sb $t0, 0",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
        asm_text_err_test!(
            "sh $t0, 0",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
        asm_text_err_test!(
            "sw $t0, 0",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
        asm_text_err_test!(
            "syscall 0",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
    }

    #[test]
    fn bad_shamt() {
        asm_text_err_test!(
            "sll $t0, $t0, 17",
            AssembleError {
                pos: 20,
                kind: AssembleErrorKind::OverflowingShamt(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: "17"
                })
            }
        );
        asm_text_err_test!(
            "sll $t0, $t0, -1",
            AssembleError {
                pos: 20,
                kind: AssembleErrorKind::OverflowingShamt(NumLiteral {
                    negative: true,
                    radix: 10,
                    body: "1"
                })
            }
        );
        asm_text_err_test!(
            "sll $t0, $t0, 50000",
            AssembleError {
                pos: 20,
                kind: AssembleErrorKind::OverflowingShamt(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: "50000"
                })
            }
        );
    }

    #[test]
    fn op_happy_paths() {
        asm_text_test!(
            "addi $t0, $zero, 18",
            new_arith_log_i(Op::ADDI, Reg::Zero, Reg::T0, 18)
        );
        asm_text_test!("lhi $t0, 37", new_load_i(Op::LHI, Reg::T0, 37));
        asm_text_test!(
            "EXIT: beq $t0, $t1, EXIT",
            new_branch(Op::BEQ, Reg::T0, Reg::T1) | -1_i16 as u16 as u32
        );
        asm_text_test!(
            "EXIT: bgtz $t0, EXIT",
            new_branch_z(Op::BGTZ, Reg::T0) | -1_i16 as u16 as u32
        );
        asm_text_test!(
            "lb $t0, 8($t1)",
            new_load_store(Op::LB, Reg::T1, Reg::T0, 8)
        );
        asm_text_test!(
            "lh $t0, 8($t1)",
            new_load_store(Op::LH, Reg::T1, Reg::T0, 8)
        );
        asm_text_test!(
            "lw $t0, 8($t1)",
            new_load_store(Op::LW, Reg::T1, Reg::T0, 8)
        );
        asm_text_test!(
            r#"
j EXIT
EXIT: syscall
            "#,
            new_jump(Op::J) | 0,
            SYSCALL
        );
        asm_text_test!("syscall", SYSCALL);
    }

    #[test]
    fn funct_happy_paths() {
        asm_text_test!(
            "add $t0, $t1, $t2",
            new_reg(Reg::T1, Reg::T2, Reg::T0, 0, Funct::ADD)
        );
        asm_text_test!(
            "mult $t0, $t1",
            new_reg(Reg::T0, Reg::T1, Reg::Zero, 0, Funct::MULT)
        );
        asm_text_test!(
            "sll $t0, $t1, 3",
            new_reg(Reg::Zero, Reg::T1, Reg::T0, 3, Funct::SLL)
        );
        asm_text_test!(
            "sllv $t0, $t1, $t2",
            new_reg(Reg::T2, Reg::T1, Reg::T0, 0, Funct::SLLV)
        );
        asm_text_test!(
            "jr $ra",
            new_reg(Reg::Ra, Reg::Zero, Reg::Zero, 0, Funct::JR)
        );
        asm_text_test!(
            "mfhi $t0",
            new_reg(Reg::Zero, Reg::Zero, Reg::T0, 0, Funct::MFHI)
        );
        asm_text_test!(
            "mthi $t0",
            new_reg(Reg::T0, Reg::Zero, Reg::Zero, 0, Funct::MTHI)
        );
    }

    #[test]
    fn data() {
        // nums
        asm_data_test!(
            r#"
a: .word 37
a: .word -37
a: .hword 3007
a: .half -3006
a: .byte -7
            "#,
            37,
            -37 as i32 as u32,
            u32::from_le_bytes([3007_u16.to_le_bytes()[0], 3007_u16.to_le_bytes()[1], 0, 0]),
            u32::from_le_bytes([
                (-3006_i16).to_le_bytes()[0],
                (-3006_i16).to_le_bytes()[1],
                0,
                0
            ]),
            u32::from_le_bytes([-7_i8 as u8, 0, 0, 0]),
        );

        // chars
        asm_data_test!("a: .byte 'a'", u32::from_le_bytes(['a' as u8, 0, 0, 0]));
        asm_data_err_test!(
            "a: .byte '😄'",
            AssembleError {
                pos: 22,
                kind: AssembleErrorKind::NonAsciiChar('😄'),
            }
        );

        // strings
        asm_data_test!(
            r#"
a: .ascii "hello world"
a: .ascii "hello\two\\ld\n"
a: .asciiz "hello\two\\ld\n"
            "#,
            str_to_u32("hell"),
            str_to_u32("o wo"),
            str_to_u32("rld\0"),
            str_to_u32("hell"),
            str_to_u32("o\two"),
            str_to_u32("\\ld\n"),
            str_to_u32("hell"),
            str_to_u32("o\two"),
            str_to_u32("\\ld\n"),
            // asciiz requires that there be at least one byte of padding
            0
        );
        asm_data_err_test!(
            "a: .ascii \"hello\\oworld\"",
            AssembleError {
                pos: 29,
                kind: AssembleErrorKind::InvalidStrEscape('o')
            }
        );
        let err = assemble(parse(".data\na: .ascii \"hello 😄\"").unwrap()).unwrap_err();
        assert_eq!(err.pos, 23);
        assert!(matches!(err.kind, AssembleErrorKind::NonAsciiStr(_)));
        let err = assemble(parse(".data\na: .asciiz \"hello 😄\"").unwrap()).unwrap_err();
        assert_eq!(err.pos, 24);
        assert!(matches!(err.kind, AssembleErrorKind::NonAsciiStr(_)));
        assert_eq!(
            assemble(Ast {
                sections: vec![Section {
                    pos: 0,
                    kind: SectionKind::Data(vec![Data {
                        pos: 0,
                        label: "",
                        decl: DataDeclaration {
                            pos: 0,
                            kind: DataKind::Ascii,
                            value_pos: 37,
                            value: DataValue::String("123\\"),
                        }
                    }])
                }],
                eof_pos: 0,
            })
            .unwrap_err(),
            AssembleError {
                pos: 42,
                kind: AssembleErrorKind::InvalidStrEscape('\\')
            }
        );

        // idents
        asm_data_test!(
            r#"
a: .word 1
b: .word 1
c: .word b
            "#,
            1,
            1,
            4
        );

        // arrays
        asm_data_test!(
            r#"
a: .word -98 : 3
a: .half -980 : 3
a: .byte -98 : 3
                    "#,
            -98_i32 as u32,
            -98_i32 as u32,
            -98_i32 as u32,
            u32::from_le_bytes([
                (-980_i16).to_le_bytes()[0],
                (-980_i16).to_le_bytes()[1],
                (-980_i16).to_le_bytes()[0],
                (-980_i16).to_le_bytes()[1],
            ]),
            u32::from_le_bytes([
                (-980_i16).to_le_bytes()[0],
                (-980_i16).to_le_bytes()[1],
                0,
                0
            ]),
            u32::from_le_bytes([
                (-98_i8).to_le_bytes()[0],
                (-98_i8).to_le_bytes()[0],
                (-98_i8).to_le_bytes()[0],
                0
            ]),
        );
        asm_data_err_test!(
            "a: .word -98 : -3",
            AssembleError {
                pos: 27,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::NegOverflow)
            }
        );

        // illegal combinations
        asm_data_err_test!(
            "a: .word 'a'",
            AssembleError {
                pos: 21,
                kind: AssembleErrorKind::IllegalDataKindValueCombination(
                    DataKind::Word,
                    DataValue::Char('a')
                )
            }
        );
        asm_data_err_test!(
            "a: .half a",
            AssembleError {
                pos: 21,
                kind: AssembleErrorKind::IllegalDataKindValueCombination(
                    DataKind::HalfWord,
                    DataValue::Ident("a")
                )
            }
        );
        asm_data_err_test!(
            "a: .byte a",
            AssembleError {
                pos: 21,
                kind: AssembleErrorKind::IllegalDataKindValueCombination(
                    DataKind::Byte,
                    DataValue::Ident("a")
                )
            }
        );
        asm_data_err_test!(
            "a: .ascii a",
            AssembleError {
                pos: 22,
                kind: AssembleErrorKind::IllegalDataKindValueCombination(
                    DataKind::Ascii,
                    DataValue::Ident("a")
                )
            }
        );
        asm_data_err_test!(
            "a: .asciiz a",
            AssembleError {
                pos: 23,
                kind: AssembleErrorKind::IllegalDataKindValueCombination(
                    DataKind::Asciiz,
                    DataValue::Ident("a")
                )
            }
        );
    }

    #[test]
    fn literal_overflows() {
        asm_text_err_test!(
            "addi $t0, $t1, 65536",
            AssembleError {
                pos: 21,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::PosOverflow)
            }
        );
        asm_text_err_test!(
            "lhi $t0, -32769",
            AssembleError {
                pos: 15,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::NegOverflow)
            }
        );
        asm_text_err_test!(
            "sb $t0, 32768($t1)",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::PosOverflow)
            }
        );
        asm_text_err_test!(
            "lhu $t0, 0xffffffffffffff($t1)",
            AssembleError {
                pos: 15,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::PosOverflow)
            }
        );
        asm_text_err_test!(
            "lw $t0, 0b1000000000000000000000000000($t1)",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::PosOverflow)
            }
        );
        asm_text_err_test!(
            "sll $t0, $t0, 0xf1",
            AssembleError {
                pos: 20,
                kind: AssembleErrorKind::OverflowingShamt(NumLiteral {
                    negative: false,
                    radix: 16,
                    body: "f1"
                })
            }
        );
        assert_eq!(
            assemble(Ast {
                sections: vec![Section {
                    pos: 0,
                    kind: SectionKind::Text(vec![Entry {
                        pos: 0,
                        kind: EntryKind::Instruction(Instruction {
                            name: "sll",
                            args: vec![
                                Argument {
                                    pos: 0,
                                    kind: ArgumentKind::Register("t0")
                                },
                                Argument {
                                    pos: 0,
                                    kind: ArgumentKind::Register("t1")
                                },
                                Argument {
                                    pos: 37,
                                    kind: ArgumentKind::Literal(Literal::Num(NumLiteral {
                                        negative: false,
                                        radix: 10,
                                        body: ""
                                    }))
                                },
                            ],
                            end_pos: 0,
                        })
                    }]),
                }],
                eof_pos: 0
            })
            .unwrap_err(),
            AssembleError {
                pos: 37,
                kind: AssembleErrorKind::ParseIntError(IntErrorKind::Empty),
            }
        );
    }

    #[test]
    fn unknown_reg() {
        asm_text_err_test!(
            "lb $t0, 4($uhoh)",
            AssembleError {
                pos: 16,
                kind: AssembleErrorKind::UnknownReg("uhoh")
            }
        );
        asm_text_err_test!(
            "lhu $t0, 0($eax)",
            AssembleError {
                pos: 17,
                kind: AssembleErrorKind::UnknownReg("eax")
            }
        );
        asm_text_err_test!(
            "lw $t0, 0($rdx)",
            AssembleError {
                pos: 16,
                kind: AssembleErrorKind::UnknownReg("rdx")
            }
        );
    }

    #[test]
    fn reference_errors() {
        asm_text_err_test!(
            "j EXIT",
            AssembleError {
                pos: 8,
                kind: AssembleErrorKind::UndefinedLabel("EXIT")
            }
        );
        asm_err_test!(
            &format!(
                r#"
    .text
la $t0, VAL
    .data
_: .word 0:{}
VAL: .byte 'v'
            "#,
                i16::MAX / 4 + 7
            ),
            AssembleError {
                pos: 19,
                kind: AssembleErrorKind::OverflowingLabelReference((i16::MAX as u32 / 4 + 8) * 4),
            }
        );
    }

    #[test]
    fn initial_jump() {
        asm_test!(
            r#"
    .data
a: .byte 'a'
    .text
syscall
            "#,
            new_jump(Op::J) | 1,
            str_to_u32("a\0\0\0"),
            SYSCALL,
        );
        asm_test!(
            r#"
    .data
    .text
syscall
            "#,
            new_jump(Op::J) | 0,
            SYSCALL,
        );
    }

    // this test is ignored by default because it requires allocating an unreasonnably large
    // program in order to cause the overflow
    #[ignore]
    #[test]
    fn initial_jump_overflow() {
        asm_err_test!(
            &format!(
                r#"
    .data
_: .word 0:{}
    .text
syscall
            "#,
                1 << 26
            ),
            AssembleError {
                pos: 35,
                kind: AssembleErrorKind::OverflowingLabelReference(1 << 26)
            }
        );
    }
}

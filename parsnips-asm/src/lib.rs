#![no_std]

use parsnips_inst::{Funct, Inst, Op};
use parsnips_parser::{
    ArgumentKind, Ast, DataKind, DataValue, EntryKind, Instruction, Literal, NumLiteral,
    ParseMaybeNeg, ParseNonNeg, SectionKind,
};

extern crate alloc;
use alloc::{string::String, vec::Vec};
use ascii::{AsAsciiStr, AsAsciiStrError};
use core::num::IntErrorKind;
use hashbrown::HashMap;
use strum_macros::EnumString;

// TODO: allow numerical register references
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

#[derive(Debug, PartialEq, Eq)]
pub enum AssembleErrorKind<'a> {
    ExpectedArgument,
    InvalidArgument(ArgumentKind<'a>),
    InvalidDestination,
    MisalignedOffset(u16),
    NoText,
    InvalidStrEscape(char),
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
}

pub fn assemble(ast: Ast) -> Result<Vec<u8>, AssembleError> {
    let mut program = Vec::new();
    let mut label_definitions = HashMap::new();
    let mut label_references = Vec::new();
    let mut initial_section_data: Option<bool> = None;
    // an optional tuple of u32 byte index within the program and usize character index within the
    // source code
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
                    match entry.value.kind {
                        DataKind::Word => match entry.value.value {
                            DataValue::Array {
                                value,
                                size_pos,
                                size,
                            } => {
                                let value =
                                    u32::parse_maybe_neg(value).map_err(|e| AssembleError {
                                        pos: size_pos,
                                        kind: AssembleErrorKind::ParseIntError(e),
                                    })?;
                                let size =
                                    usize::parse_non_neg(size).map_err(|e| AssembleError {
                                        pos: size_pos,
                                        kind: AssembleErrorKind::ParseIntError(e),
                                    })?;
                                program.reserve(size * 4);
                                let le_bytes = value.to_le_bytes();
                                for _ in 0..size {
                                    program.extend_from_slice(&le_bytes);
                                }
                            }
                            DataValue::Int(value) => {
                                program.extend_from_slice(
                                    &u32::parse_maybe_neg(value)
                                        .map_err(|e| AssembleError {
                                            pos: entry.value.pos,
                                            kind: AssembleErrorKind::ParseIntError(e),
                                        })?
                                        .to_le_bytes(),
                                );
                            }
                            _ => todo!(),
                        },
                        DataKind::HalfWord => todo!(),
                        DataKind::Byte => todo!(),
                        DataKind::Ascii => todo!(),
                        DataKind::Asciiz => match entry.value.value {
                            DataValue::String(value) => {
                                let mut unescaped = String::new();
                                let mut ci = value.chars().enumerate();
                                while let Some((pos, c)) = ci.next() {
                                    unescaped.push(match c {
                                        '\\' => match ci.next() {
                                            Some((_, 't')) => '\t',
                                            Some((_, 'n')) => '\n',
                                            Some((_, '\\')) => '\\',
                                            Some((_, c)) => {
                                                return Err(AssembleError {
                                                    pos,
                                                    kind: AssembleErrorKind::InvalidStrEscape(c),
                                                })
                                            }
                                            None => {
                                                // this error maybe isn't really the most
                                                // appropriate thing for this case, but this error
                                                // case shouldn't occur with a well-formed AST
                                                // produced by lex and parse anyways so...
                                                return Err(AssembleError {
                                                    pos: pos + 1,
                                                    kind: AssembleErrorKind::InvalidStrEscape(c),
                                                });
                                            }
                                        },
                                        o => o,
                                    })
                                }

                                let str_bytes = unescaped
                                    .as_ascii_str()
                                    .map_err(|e| AssembleError {
                                        pos: e.valid_up_to(),
                                        kind: AssembleErrorKind::NonAsciiStr(e),
                                    })?
                                    .as_bytes();
                                program.extend_from_slice(str_bytes);
                                // TODO: revisit this, is this how other things do this?
                                // Ensure word alignment is preserved
                                for _ in 0..4 - (str_bytes.len() % 4) {
                                    program.push(0);
                                }
                            }
                            _ => todo!(),
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
                                                    u16::parse_maybe_neg(lit).map_err(|e| {
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
                                                u16::parse_maybe_neg(lit).map_err(|e| {
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
                                                        kind: AssembleErrorKind::UnknownReg(name),
                                                    }
                                                })?,
                                                rt,
                                                u16::parse_maybe_neg(offset).map_err(|e| {
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
                                                u16::parse_maybe_neg(offset).map_err(|e| {
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
                                                        kind: AssembleErrorKind::UnknownReg(name),
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
                                                u16::parse_maybe_neg(offset).map_err(|e| {
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
                                                        kind: AssembleErrorKind::UnknownReg(name),
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
                                        match u8::parse_non_neg(shamt_lit.clone()) {
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
                                                })
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
                                                u16::parse_maybe_neg(lit).map_err(|e| {
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
        }
        .map_err(|kind| AssembleError {
            pos: reference.pos,
            kind,
        })?;
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
    use alloc::borrow::ToOwned;
    use parsnips_parser::parse;
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
            asm_test!(&("    .text\n".to_owned() + $s), $($x),+)
        }
    }

    macro_rules! asm_err_text_test {
        ($s:expr,$err:expr) => {
            asm_err_test!(&("    .text\n".to_owned() + $s), $err)
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
        asm_err_text_test!(
            "addi $zero, $zero, 0",
            AssembleError {
                pos: 15,
                kind: AssembleErrorKind::InvalidDestination
            }
        );
        asm_err_text_test!(
            "lhi $zero, 94",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::InvalidDestination
            }
        );
        asm_err_text_test!(
            "add $zero, $zero, $zero",
            AssembleError {
                pos: 14,
                kind: AssembleErrorKind::InvalidDestination
            }
        );
    }

    #[test]
    fn unknown_instruction() {
        asm_err_text_test!(
            "reg $t0, $t0, $t0",
            AssembleError {
                pos: 10,
                kind: AssembleErrorKind::UnknownInstruction("reg")
            }
        );
        asm_err_text_test!(
            "bogus $t0, $t0, $t0",
            AssembleError {
                pos: 10,
                kind: AssembleErrorKind::UnknownInstruction("bogus")
            }
        );
        // identifiers are case sensitive
        asm_err_text_test!(
            "ADD $t0, $t0, $t0",
            AssembleError {
                pos: 10,
                kind: AssembleErrorKind::UnknownInstruction("ADD")
            }
        );
    }

    #[test]
    fn redeclared_label() {
        asm_err_text_test!(
            r#"
EXIT:
EXIT:
            "#,
            AssembleError {
                pos: 17,
                kind: AssembleErrorKind::RedeclaredLabel("EXIT")
            }
        );
        asm_err_text_test!(
            r#"
EXIT:
    .text
EXIT:
            "#,
            AssembleError {
                pos: 27,
                kind: AssembleErrorKind::RedeclaredLabel("EXIT")
            }
        );
    }

    #[test]
    fn misaligned_offset() {
        asm_err_text_test!(
            "lh $t0, 1($t1)",
            AssembleError {
                pos: 18,
                kind: AssembleErrorKind::MisalignedOffset(1)
            }
        );
        asm_err_text_test!(
            "lw $t0, 2($t1)",
            AssembleError {
                pos: 18,
                kind: AssembleErrorKind::MisalignedOffset(2)
            }
        );
    }

    #[test]
    fn unexpected_arg() {
        asm_err_text_test!(
            "addi $t0, $zero, 4, 9",
            AssembleError {
                pos: 30,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "9"
                    }
                )))
            }
        );
        asm_err_text_test!(
            "sb $t0, 0",
            AssembleError {
                pos: 18,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
        asm_err_text_test!(
            "sh $t0, 0",
            AssembleError {
                pos: 18,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
        asm_err_text_test!(
            "sw $t0, 0",
            AssembleError {
                pos: 18,
                kind: AssembleErrorKind::UnexpectedArgument(ArgumentKind::Literal(Literal::Num(
                    NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "0"
                    }
                )))
            }
        );
        asm_err_text_test!(
            "syscall 0",
            AssembleError {
                pos: 18,
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
        asm_err_text_test!(
            "sll $t0, $t0, 17",
            AssembleError {
                pos: 24,
                kind: AssembleErrorKind::OverflowingShamt(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: "17"
                })
            }
        );
        asm_err_text_test!(
            "sll $t0, $t0, -1",
            AssembleError {
                pos: 24,
                kind: AssembleErrorKind::OverflowingShamt(NumLiteral {
                    negative: true,
                    radix: 10,
                    body: "1"
                })
            }
        );
        asm_err_text_test!(
            "sll $t0, $t0, 50000",
            AssembleError {
                pos: 24,
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
        asm_text_test!("syscall", SYSCALL)
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
}

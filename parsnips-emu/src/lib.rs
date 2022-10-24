#![no_std]
#![deny(clippy::cast_possible_truncation)]

// TODO: fix the assumption that usize is at least as big as a u32. This isn't
// true on some platforms, such as msp430-none-elf

#[cfg(target_arch = "wasm32")]
mod error {
    use core::{fmt, str::from_utf8_unchecked};
    use wasm_bindgen::JsValue;

    pub type ErrorType = JsValue;

    // source: https://stackoverflow.com/a/50201632
    pub struct JsStrWriter<'a> {
        buf: &'a mut [u8],
        used: usize,
    }
    impl<'a> JsStrWriter<'a> {
        pub fn new(buf: &'a mut [u8]) -> Self {
            Self { buf, used: 0 }
        }

        pub fn as_js_value(self) -> JsValue {
            JsValue::from_str(unsafe { from_utf8_unchecked(&self.buf[..self.used]) })
        }
    }
    impl<'a> fmt::Write for JsStrWriter<'a> {
        fn write_str(&mut self, str: &str) -> fmt::Result {
            let rem_buf = &mut self.buf[self.used..];
            let str_bytes = str.as_bytes();
            if str_bytes.len() <= rem_buf.len() {
                rem_buf[..str_bytes.len()].copy_from_slice(&str_bytes);
                self.used += str_bytes.len();
                Ok(())
            } else {
                Err(fmt::Error)
            }
        }
    }

    #[macro_export]
    macro_rules! ERR_FUNCT {
        ($x:expr) => {{
            let mut buf: [u8; 25] = [0; 25];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(&mut w, format_args!("invalid function {:#08b}", $x)).unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_OP {
        ($x:expr) => {{
            let mut buf: [u8; 23] = [0; 23];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(&mut w, format_args!("invalid opcode {:#08b}", $x)).unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_OOB {
        ($x:expr, $y:expr) => {{
            let mut buf: [u8; 74] = [0; 74];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(
                &mut w,
                format_args!(
                    "program counter {} out of bounds for max memory address {}",
                    $x, $y
                ),
            )
            .unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_OVERFLOW {
        () => {
            JsValue::from_str("overflow occurred")
        };
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_LH {
        ($x:expr) => {{
            let mut buf: [u8; 60] = [0; 60];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(
                &mut w,
                format_args!("misaligned load-half from {:#034b}", $x),
            )
            .unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_LW {
        ($x:expr) => {{
            let mut buf: [u8; 60] = [0; 60];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(
                &mut w,
                format_args!("misaligned load-word from {:#034b}", $x),
            )
            .unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_SH {
        ($x:expr) => {{
            let mut buf: [u8; 58] = [0; 58];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(&mut w, format_args!("misaligned save-half to {:#034b}", $x)).unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_SW {
        ($x:expr) => {{
            let mut buf: [u8; 58] = [0; 58];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(&mut w, format_args!("misaligned save-word to {:#034b}", $x)).unwrap();
            w.as_js_value()
        }};
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_PC {
        ($x:expr) => {{
            let mut buf: [u8; 61] = [0; 61];
            let mut w = JsStrWriter::new(&mut buf[..]);
            core::fmt::write(
                &mut w,
                format_args!("misaligned program counter {:#034b}", $x),
            )
            .unwrap();
            w.as_js_value()
        }};
    }
}
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(not(target_arch = "wasm32"))]
mod error {
    #[cfg(feature = "std")]
    use std::{error::Error, fmt};

    pub type ErrorType = EmulatorError;

    #[derive(Debug)]
    pub enum EmulatorError {
        InvalidFunction(u8),
        InvalidOpcode(u8),
        OutOfBounds { pc: u32, max: usize },
        Overflow,
        MisalignedLH(u32),
        MisalignedLW(u32),
        MisalignedSH(u32),
        MisalignedSW(u32),
        MisalignedPC(u32),
    }
    #[cfg(feature = "std")]
    impl fmt::Display for EmulatorError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::InvalidFunction(funct) => write!(f, "invalid function {:#08b}", funct),
                Self::InvalidOpcode(op) => write!(f, "invalid opcode {:#08b}", op),
                Self::OutOfBounds { pc, max } => {
                    write!(
                        f,
                        "program counter {} out of bounds for max memory address {}",
                        pc, max
                    )
                }
                Self::Overflow => write!(f, "overflow occurred"),
                Self::MisalignedLH(addr) => write!(f, "misaligned load-half from {:#034b}", addr),
                Self::MisalignedLW(addr) => write!(f, "misaligned load-word from {:#034b}", addr),
                Self::MisalignedSH(addr) => write!(f, "misaligned save-half to {:#034b}", addr),
                Self::MisalignedSH(addr) => write!(f, "misaligned save-half to {:#034b}", addr),
                Self::MisalignedPC(addr) => write!(f, "misaligned program counter {:#034b}", addr),
            }
        }
    }
    #[cfg(feature = "std")]
    impl Error for EmulatorError {}

    #[macro_export]
    macro_rules! ERR_FUNCT {
        ($x:expr) => {
            EmulatorError::InvalidFunction($x)
        };
    }
    #[macro_export]
    macro_rules! ERR_OP {
        ($x:expr) => {
            EmulatorError::InvalidOpcode($x)
        };
    }
    #[macro_export]
    macro_rules! ERR_OOB {
        ($x:expr, $y:expr) => {
            EmulatorError::OutOfBounds { pc: $x, max: $y }
        };
    }
    #[macro_export]
    macro_rules! ERR_OVERFLOW {
        () => {
            EmulatorError::Overflow
        };
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_LH {
        ($x:expr) => {
            EmulatorError::MisalignedLH($x)
        };
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_LW {
        ($x:expr) => {
            EmulatorError::MisalignedLW($x)
        };
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_SH {
        ($x:expr) => {
            EmulatorError::MisalignedSH($x)
        };
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_SW {
        ($x:expr) => {
            EmulatorError::MisalignedSW($x)
        };
    }
    #[macro_export]
    macro_rules! ERR_MISALIGNED_PC {
        ($x:expr) => {
            EmulatorError::MisalignedPC($x)
        };
    }
}

use error::*;
use parsnips_util as util;
use util::{inst, IndexAligned, IndexAlignedMut};

const MASK8: u32 = (1 << 8) - 1;
const MASK16: u32 = (1 << 16) - 1;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Emulator {
    // TODO: figure out what $gp and $fp should be initialized to
    regs: [u32; 32],
    // PERF: consider refactoring to a single u64
    lo: u32,
    hi: u32,
    pc: u32,
}

impl Default for Emulator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl Emulator {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new() -> Self {
        Self {
            regs: [0; 32],
            lo: 0,
            hi: 0,
            pc: 0,
        }
    }

    pub fn get_reg(&self, reg: usize) -> u32 {
        self.regs[reg]
    }

    // NOTE: step must take memory as parameter instead of it being provided
    // it to Emulator::new because wasm_bindgen values cannot have lifetimes

    pub fn step(&mut self, memory: &mut [u8]) -> Result<bool, ErrorType> {
        if self.pc as usize >= memory.len() {
            return Err(ERR_OOB![self.pc, memory.len() - 4]);
        }
        let inst = if self.pc % 4 == 0 {
            util::Inst::from_le(unsafe { memory.index_aligned(self.pc as usize) })
        } else {
            return Err(ERR_MISALIGNED_PC![self.pc]);
        };
        self.pc += 4;

        use inst::opcode::*;
        match inst::InstFields::op(&inst) {
            REG => {
                use inst::funct::*;
                use inst::RegFields;

                match inst.funct() {
                    // NOTE: the difference between ADD and ADDU is that ADD
                    // generates a trap when an overflow occurs, so it is
                    // correct to use the unsafe u32::unchecked_add for ADDU
                    // and ADDIU because overflows in those operations are
                    // allowed
                    ADD => {
                        use inst::ArithLogFields;

                        match (self.regs[inst.rs()] as i32).checked_add(self.regs[inst.rt()] as i32)
                        {
                            Some(s) => self.regs[inst.rd()] = s as u32,
                            None => return Err(ERR_OVERFLOW![]),
                        };
                    }
                    ADDU => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] =
                            self.regs[inst.rs()].overflowing_add(self.regs[inst.rt()]).0;
                    }
                    AND => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] = self.regs[inst.rs()] & self.regs[inst.rt()];
                    }
                    DIV => {
                        use inst::DivMultFields;

                        self.lo =
                            (self.regs[inst.rs()] as i32 / self.regs[inst.rt()] as i32) as u32;
                        self.hi =
                            (self.regs[inst.rs()] as i32 % self.regs[inst.rt()] as i32) as u32;
                    }
                    DIVU => {
                        use inst::DivMultFields;

                        self.lo = self.regs[inst.rs()] / self.regs[inst.rt()];
                        self.hi = self.regs[inst.rs()] % self.regs[inst.rt()];
                    }
                    // PERF: investigate whether there's a faster way to do these two operations.
                    // Can I do some transmutation with i64's? How does that play with endianness?
                    MULT => {
                        use inst::DivMultFields;

                        let res =
                            self.regs[inst.rs()] as i32 as i64 * self.regs[inst.rt()] as i32 as i64;
                        // these unwraps are safe because the preceeding operations will verify
                        // that things are in bounds
                        self.hi = i32::try_from(res / (1_i64 << 32)).unwrap() as u32;
                        self.lo = i32::try_from(res % (1_i64 << 32)).unwrap() as u32;
                    }
                    MULTU => {
                        use inst::DivMultFields;

                        let res = self.regs[inst.rs()] as u64 * self.regs[inst.rt()] as u64;
                        #[allow(clippy::cast_possible_truncation)]
                        {
                            self.hi = (res / (u32::MAX as u64 + 1)) as u32;
                            self.lo = (res % (u32::MAX as u64 + 1)) as u32;
                        }
                    }
                    NOR => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] = !(self.regs[inst.rs()] | self.regs[inst.rt()]);
                    }
                    OR => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] = self.regs[inst.rs()] | self.regs[inst.rt()];
                    }
                    XOR => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] = self.regs[inst.rs()] ^ self.regs[inst.rt()];
                    }
                    MFHI => {
                        use inst::MoveFromFields;

                        self.regs[inst.rd()] = self.hi;
                    }
                    MFLO => {
                        use inst::MoveFromFields;

                        self.regs[inst.rd()] = self.lo;
                    }
                    MTHI => {
                        use inst::MoveToFields;

                        self.hi = self.regs[inst.rs()];
                    }
                    MTLO => {
                        use inst::MoveToFields;

                        self.lo = self.regs[inst.rs()];
                    }
                    SLL => {
                        use inst::ShiftFields;

                        self.regs[inst.rd()] = self.regs[inst.rt()] << inst.shamt();
                    }
                    SLLV => {
                        use inst::ShiftVFields;

                        self.regs[inst.rd()] = self.regs[inst.rt()] << self.regs[inst.rs()];
                    }
                    SRA => {
                        use inst::ShiftFields;

                        self.regs[inst.rd()] = (self.regs[inst.rt()] as i32 >> inst.shamt()) as u32;
                    }
                    SRAV => {
                        use inst::ShiftVFields;

                        self.regs[inst.rd()] =
                            (self.regs[inst.rt()] as i32 >> self.regs[inst.rs()]) as u32;
                    }
                    SRL => {
                        use inst::ShiftFields;

                        self.regs[inst.rd()] = self.regs[inst.rt()] >> inst.shamt();
                    }
                    SRLV => {
                        use inst::ShiftVFields;

                        self.regs[inst.rd()] = self.regs[inst.rt()] >> self.regs[inst.rs()];
                    }
                    SUB => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] =
                            (self.regs[inst.rs()] as i32 - self.regs[inst.rt()] as i32) as u32;
                    }
                    SUBU => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] = self.regs[inst.rs()] - self.regs[inst.rt()];
                    }
                    JR => {
                        use inst::JumpRFields;

                        self.pc = self.regs[inst.rs()];
                    }
                    JALR => {
                        use inst::JumpRFields;

                        self.regs[31] = self.pc;
                        self.pc = self.regs[inst.rs()];
                    }
                    SLT => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] =
                            if (self.regs[inst.rs()] as i32) < (self.regs[inst.rt()] as i32) {
                                1
                            } else {
                                0
                            };
                    }
                    SLTU => {
                        use inst::ArithLogFields;

                        self.regs[inst.rd()] = if self.regs[inst.rs()] < self.regs[inst.rt()] {
                            1
                        } else {
                            0
                        };
                    }
                    unknown => return Err(ERR_FUNCT![unknown]),
                }
            }
            ADDI => {
                use inst::ArithLogIFields;

                match (self.regs[inst.rs()] as i32).checked_add(inst.imm() as i16 as i32) {
                    Some(s) => self.regs[inst.rt()] = s as u32,
                    None => return Err(ERR_OVERFLOW![]),
                };
            }
            ADDIU => {
                use inst::ArithLogIFields;

                self.regs[inst.rt()] = self.regs[inst.rs()].overflowing_add(inst.imm() as u32).0;
            }
            ANDI => {
                use inst::ArithLogIFields;

                self.regs[inst.rt()] = self.regs[inst.rs()] & inst.imm() as u32;
            }
            ORI => {
                use inst::ArithLogIFields;

                self.regs[inst.rt()] = self.regs[inst.rs()] | inst.imm() as u32;
            }
            XORI => {
                use inst::ArithLogIFields;

                self.regs[inst.rt()] = self.regs[inst.rs()] ^ inst.imm() as u32;
            }
            // PERF: figure out if unsafe and pointer hyjinks can speed LHI and LLO up
            LHI => {
                use inst::LoadIFields;

                self.regs[inst.rt()] &= u16::MAX as u32;
                self.regs[inst.rt()] |= (inst.imm() as u32) << 16;
            }
            LLO => {
                use inst::LoadIFields;

                self.regs[inst.rt()] &= (u16::MAX as u32) << 16;
                self.regs[inst.rt()] |= inst.imm() as u32;
            }
            J => {
                use inst::JumpFields;

                self.pc = (self.pc as i32 + inst.imm()) as u32;
            }
            JAL => {
                use inst::JumpFields;

                self.regs[31] = self.pc;
                self.pc = (self.pc as i32 + inst.imm()) as u32;
            }
            SLTI => {
                use inst::ArithLogIFields;

                self.regs[inst.rt()] = if (self.regs[inst.rs()] as i32) < (inst.imm() as i16 as i32)
                {
                    1
                } else {
                    0
                };
            }
            SLTIU => {
                use inst::ArithLogIFields;

                self.regs[inst.rt()] = if self.regs[inst.rs()] < inst.imm() as u32 {
                    1
                } else {
                    0
                };
            }
            BEQ => {
                use inst::BranchFields;

                if self.regs[inst.rs()] == self.regs[inst.rt()] {
                    self.pc = (self.pc as i32 + inst.imm() as i32) as u32;
                }
            }
            BNE => {
                use inst::BranchFields;

                if self.regs[inst.rs()] != self.regs[inst.rt()] {
                    self.pc = (self.pc as i32 + inst.imm() as i32) as u32;
                }
            }
            BLEZ => {
                use inst::BranchZFields;

                if self.regs[inst.rs()] as i32 <= 0 {
                    self.pc = (self.pc as i32 + inst.imm()) as u32;
                }
            }
            BGTZ => {
                use inst::BranchZFields;

                if self.regs[inst.rs()] as i32 > 0 {
                    self.pc = (self.pc as i32 + inst.imm()) as u32;
                }
            }
            LB => {
                use inst::LoadStoreFields;

                self.regs[inst.rt()] =
                    memory[(self.regs[inst.rs()] as i32 + inst.imm()) as usize] as i8 as i32 as u32;
            }
            LBU => {
                use inst::LoadStoreFields;

                self.regs[inst.rt()] =
                    memory[(self.regs[inst.rs()] as i32 + inst.imm()) as usize] as u32;
            }
            LH => {
                use inst::LoadStoreFields;

                let addr = (self.regs[inst.rs()] as i32 + inst.imm()) as u32;
                if addr % 2 == 0 {
                    self.regs[inst.rt()] =
                        u16::from_le(unsafe { memory.index_aligned(addr as usize) }) as i16 as i32
                            as u32;
                } else {
                    return Err(ERR_MISALIGNED_LH![addr]);
                }
            }
            LHU => {
                use inst::LoadStoreFields;

                let addr = (self.regs[inst.rs()] as i32 + inst.imm()) as u32;
                if addr % 2 == 0 {
                    self.regs[inst.rt()] =
                        u16::from_le(unsafe { memory.index_aligned(addr as usize) }) as u32;
                } else {
                    return Err(ERR_MISALIGNED_LH![addr]);
                }
            }
            LW => {
                use inst::LoadStoreFields;

                let addr = (self.regs[inst.rs()] as i32 + inst.imm()) as u32;
                if addr % 4 == 0 {
                    self.regs[inst.rt()] =
                        u32::from_le(unsafe { memory.index_aligned(addr as usize) });
                } else {
                    return Err(ERR_MISALIGNED_LW![addr]);
                }
            }
            SB => {
                use inst::LoadStoreFields;

                memory[(self.regs[inst.rs()] as i32 + inst.imm()) as usize] =
                    (self.regs[inst.rt()] & MASK8) as u8;
            }
            SH => {
                use inst::LoadStoreFields;

                let addr = (self.regs[inst.rs()] as i32 + inst.imm()) as u32;
                if addr % 2 == 0 {
                    *unsafe { memory.as_mut().index_aligned_mut(addr as usize) } =
                        ((self.regs[inst.rt()] & MASK16) as u16).to_le();
                } else {
                    return Err(ERR_MISALIGNED_SH![addr]);
                }
            }
            SW => {
                use inst::LoadStoreFields;

                let addr = (self.regs[inst.rs()] as i32 + inst.imm()) as u32;
                if addr % 4 == 0 {
                    *unsafe { memory.as_mut().index_aligned_mut(addr as usize) } =
                        self.regs[inst.rt()];
                } else {
                    return Err(ERR_MISALIGNED_SW![addr]);
                }
            }
            SYSCALL => {
                return Ok(true);
            }
            unknown => return Err(ERR_OP![unknown]),
        };

        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use util::le_byte_arr;
    use wasm_bindgen_test::wasm_bindgen_test;

    #[test]
    #[wasm_bindgen_test]
    fn add_pos() {
        let mut prog = le_byte_arr![
            0b001000_00000_00011_0000000000000000 | 2,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00010_00011_00100_00101_100000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], 3);
    }
    #[test]
    #[wasm_bindgen_test]
    fn add_neg() {
        let mut prog = le_byte_arr![
            0b001000_00000_00011_0000000000000000 | (-1_i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (-1_i16 as u16 as u32),
            0b000000_00010_00011_00100_00101_100000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], -2_i32 as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn add_big() {
        let mut prog = le_byte_arr![
            0b001000_00000_00011_0000000000000000 | (i16::MAX as u32),
            0b001000_00000_00010_0000000000000000 | (i16::MAX as u32),
            0b000000_00010_00011_00100_00101_100000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], u16::MAX as u32 - 1);
    }
    #[test]
    #[wasm_bindgen_test]
    fn add_overflow() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000000_00000_00001_00010_11111_000000,
            0b000000_00000_00001_00011_11111_000000,
            0b000000_00010_00011_00100_00000_100000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) => v.as_string().unwrap() == "overflow occurred",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::Overflow) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn addu_small() {
        let mut prog = le_byte_arr![
            0b001001_00000_00011_0000000000000000 | 2,
            0b001001_00000_00010_0000000000000000 | 1,
            0b000000_00010_00011_00100_00101_100001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], 3);
    }
    #[test]
    #[wasm_bindgen_test]
    fn addu_big() {
        let mut prog = le_byte_arr![
            0b001001_00000_00011_0000000000000000 | (u16::MAX as u32),
            0b001001_00000_00010_0000000000000000 | (u16::MAX as u32),
            0b000000_00010_00011_00100_00101_100001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], u16::MAX as u32 * 2);
    }

    #[test]
    #[wasm_bindgen_test]
    fn and() {
        let mut prog = le_byte_arr![
            0b001001_00000_00011_1000001101101001,
            0b001001_00000_00010_1011000100111011,
            0b000000_00010_00011_00100_00101_100100,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], 0b1000000100101001);
    }

    // TODO: add tests that highlight the difference between div and divu

    #[test]
    #[wasm_bindgen_test]
    fn div() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 11,
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, 2);
        assert_eq!(emu.hi, 3);
    }

    #[test]
    #[wasm_bindgen_test]
    fn divu() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 11,
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, 2);
        assert_eq!(emu.hi, 3);
    }

    #[test]
    #[wasm_bindgen_test]
    fn mult_pos() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 11,
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, 44);
        assert_eq!(emu.hi, 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn mult_neg() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | (-11_i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, -44_i32 as u32);
        assert_eq!(emu.hi, 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn mult_big() {
        // TODO: make these bigger when shifts are added
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | (i16::MAX as u32),
            0b001000_00000_00010_0000000000000000 | (i16::MAX as u32),
            0b000000_00001_00010_0000000000_011000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, i16::MAX as u32 * i16::MAX as u32);
        assert_eq!(emu.hi, 0);
    }

    #[test]
    #[wasm_bindgen_test]
    fn multu_small() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 7,
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00001_00010_0000000000_011001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, 21);
        assert_eq!(emu.hi, 0);
    }

    #[test]
    #[wasm_bindgen_test]
    fn multu_big() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | (-1_i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (-1_i16 as u16 as u32),
            0b000000_00001_00010_0000000000_011001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, 1);
        assert_eq!(emu.hi, 4294967294);
    }

    #[test]
    #[wasm_bindgen_test]
    fn nor() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_1100000100001101,
            0b001001_00000_00010_1010101000101100,
            0b000000_00001_00010_00011_00000_100111,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0b0001010011010010);
    }

    #[test]
    #[wasm_bindgen_test]
    fn or() {
        let mut prog = le_byte_arr![
            0b001001_00000_00001_1100000100001101,
            0b001001_00000_00010_1010101000101100,
            0b000000_00001_00010_00011_00000_100101,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0b1110101100101101);
    }

    #[test]
    #[wasm_bindgen_test]
    fn ori() {
        let mut prog = le_byte_arr![
            0b001001_00000_00001_1100000100001101,
            0b001101_00001_00010_1010101000101100,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0b1110101100101101);
    }

    #[test]
    #[wasm_bindgen_test]
    fn xor() {
        let mut prog = le_byte_arr![
            0b001001_00000_00001_1100000100001101,
            0b001001_00000_00010_1010101000101100,
            0b000000_00001_00010_00011_00000_100110,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0b0110101100100001);
    }

    #[test]
    #[wasm_bindgen_test]
    fn xori() {
        let mut prog = le_byte_arr![
            0b001001_00000_00001_1100000100001101,
            0b001110_00001_00010_1010101000101100,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0b0110101100100001);
    }

    #[test]
    #[wasm_bindgen_test]
    fn lhi() {
        let mut prog = le_byte_arr![0b011001_00000_00001_0000000000000000 | 17];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 17 << 16);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lhi_then_llo() {
        let mut prog = le_byte_arr![
            0b011001_00000_00001_0000000000000000 | 17,
            0b011000_00000_00001_0000000000000000 | 17,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], (17 << 16) + 17);
    }

    #[test]
    #[wasm_bindgen_test]
    fn llo() {
        let mut prog = le_byte_arr![0b011000_00000_00001_0000000000000000 | 17];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 17);
    }
    #[test]
    #[wasm_bindgen_test]
    fn llo_then_lhi() {
        let mut prog = le_byte_arr![
            0b011000_00000_00001_0000000000000000 | 17,
            0b011001_00000_00001_0000000000000000 | 17,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], (17 << 16) + 17);
    }

    #[test]
    #[wasm_bindgen_test]
    fn mtfhi() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 31,
            0b000000_00001_00000_00000_00000_010001,
            0b000000_00000_00000_00010_00000_010000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.hi, 31);
        assert_eq!(emu.regs[2], 31);
    }

    #[test]
    #[wasm_bindgen_test]
    fn mtflo() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 31,
            0b000000_00001_00000_00000_00000_010011,
            0b000000_00000_00000_00010_00000_010010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, 31);
        assert_eq!(emu.regs[2], 31);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sll() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 31,
            0b000000_00000_00001_00001_00111_000000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 31 << 7);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sllv() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 31,
            0b001000_00000_00010_0000000000000000 | 7,
            0b000000_00010_00001_00001_00000_000100,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 31 << 7);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sra() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | ((-2_i16 << 4) as u16 as u32),
            0b000000_00000_00001_00001_00011_000011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], (-2_i32 << 1) as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn srav() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | ((-2_i16 << 4) as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00010_00001_00001_00000_000111,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], (-2_i32 << 1) as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn srl() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | (31 << 6),
            0b000000_00000_00001_00001_00011_000010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 31 << 3);
    }
    #[test]
    #[wasm_bindgen_test]
    fn srl_not_extended() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | ((-2_i16 << 4) as u16 as u32),
            0b000000_00000_00001_00001_01111_000010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], (-2_i32 << 4) as u32 >> 15);
    }

    #[test]
    #[wasm_bindgen_test]
    fn srlv() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | (31 << 6),
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00010_00001_00001_00000_000110,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 31 << 3);
    }
    #[test]
    #[wasm_bindgen_test]
    fn srlv_not_extended() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | ((-2_i16 << 4) as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 15,
            0b000000_00010_00001_00001_00000_000110,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], (-2_i32 << 4) as u32 >> 15);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sub_pos() {
        let minuend = 159;
        let subtrahend = 61;
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | minuend,
            0b001000_00000_00010_0000000000000000 | subtrahend,
            0b000000_00001_00010_00011_00000_100010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], minuend - subtrahend);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sub_neg() {
        let minuend = -61_i16;
        let subtrahend = -159_i16;
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | minuend as u16 as u32,
            0b001000_00000_00010_0000000000000000 | subtrahend as u16 as u32,
            0b000000_00001_00010_00011_00000_100010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], (minuend - subtrahend) as i32 as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn subu_pos() {
        let minuend = 159;
        let subtrahend = 61;
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | minuend,
            0b001000_00000_00010_0000000000000000 | subtrahend,
            0b000000_00001_00010_00011_00000_100011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], minuend - subtrahend);
    }
    #[test]
    #[wasm_bindgen_test]
    fn subu_neg() {
        let minuend = -61_i16;
        let subtrahend = -159_i16;
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | minuend as u16 as u32,
            0b001000_00000_00010_0000000000000000 | subtrahend as u16 as u32,
            0b000000_00001_00010_00011_00000_100011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(
            emu.regs[3],
            minuend as i32 as u32 - subtrahend as i32 as u32
        );
    }

    #[test]
    #[wasm_bindgen_test]
    fn addi_pos() {
        let mut prog = le_byte_arr![0b001000_00000_00001_0000000000000000 | (i16::MAX as u32)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], i16::MAX as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn addi_neg() {
        let mut prog = le_byte_arr![0b001000_00000_00001_0000000000000000 | (-1_i16 as u16 as u32)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -1_i16 as i32 as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn addi_overflow() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000000_00000_00001_00010_11111_000000,
            0b000000_00000_00001_00011_11111_000000,
            0b001000_00010_00010_1111111111111111,
            0b000000_00010_00011_00100_00000_100000,
            0b001000_00100_00100_1111111111111111,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) => v.as_string().unwrap() == "overflow occurred",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::Overflow) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn addiu_small() {
        let mut prog = le_byte_arr![0b001001_00000_00001_0000000000000000 | 7];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 7);
    }
    #[test]
    #[wasm_bindgen_test]
    fn addiu_big() {
        let mut prog = le_byte_arr![0b001001_00000_00001_0000000000000000 | (u16::MAX as u32)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], u16::MAX as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn andi() {
        let mut prog = le_byte_arr![
            0b001001_00000_00001_1000001101101001,
            0b001100_00001_00010_1011000100111011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0b1000000100101001);
    }

    #[test]
    #[wasm_bindgen_test]
    fn j() {
        let mut prog = le_byte_arr![
            0b001000_00001_00001_0000000000000000 | 1,
            // jump negative 8 relative to what the PC would become, back to the
            // first instruction
            0b000010_11111111111111111111111110,
            0b001000_00000_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 2);
        assert_eq!(emu.regs[2], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn j_outofbounds() {
        let mut prog = le_byte_arr![
            0b000010_00000000000000000000100000,
            0b000000_00000_00000_0000000000000000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "program counter 132 out of bounds for max memory address 4",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::OutOfBounds { pc: 132, max: 4 }) => true,
                _ => false,
            });
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn jr() {
        let mut prog = le_byte_arr![
            0b001000_00001_00001_0000000000000000 | 1,
            // jump to position 0
            0b000000_00000_00000_00000_00000_001000,
            0b001000_00000_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 2);
        assert_eq!(emu.regs[2], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn jr_misaligned_pc() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000000_00001_00000_00000_00000_001000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "misaligned program counter 0b00000000000000000000000000000001",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::MisalignedPC(0b00000000000000000000000000000001)) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn jal() {
        let mut prog = le_byte_arr![
            0b001000_00001_00001_0000000000000000 | 1,
            // jump negative 8 relative to what the PC would become, back to the
            // first instruction
            0b000011_11111111111111111111111110,
            0b001000_00000_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 2);
        assert_eq!(emu.regs[2], 0);
        assert_eq!(emu.regs[31], 8);
    }

    #[test]
    #[wasm_bindgen_test]
    fn jalr() {
        let mut prog = le_byte_arr![
            0b001000_00001_00001_0000000000000000 | 1,
            // jump to position 0
            0b000000_00000_00000_00000_00000_001001,
            0b001000_00000_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 2);
        assert_eq!(emu.regs[2], 0);
        assert_eq!(emu.regs[31], 8);
    }

    #[test]
    #[wasm_bindgen_test]
    fn slt_lt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001000_00000_00010_0000000000000000 | 2,
            0b000000_00001_00010_00011_00000_101010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 1);
    }
    #[test]
    #[wasm_bindgen_test]
    fn slt_eq() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00001_00010_00011_00000_101010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn slt_gt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 2,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00001_00010_00011_00000_101010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn slt_neg() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | -1_i16 as u16 as u32,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00001_00010_00011_00000_101010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 1);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sltu_lt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001000_00000_00010_0000000000000000 | 2,
            0b000000_00001_00010_00011_00000_101001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 1);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sltu_eq() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00001_00010_00011_00000_101001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sltu_gt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 2,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00001_00010_00011_00000_101001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sltu_neg() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | -1_i16 as u16 as u32,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00001_00010_00011_00000_101001,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[3], 0);
    }

    #[test]
    #[wasm_bindgen_test]
    fn slti_lt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001010_00001_00010_0000000000000000 | 2,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 1);
    }
    #[test]
    #[wasm_bindgen_test]
    fn slti_eq() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001010_00001_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn slti_gt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 2,
            0b001010_00001_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn slti_neg() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | -1_i16 as u16 as u32,
            0b001010_00001_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 1);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sltiu_lt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001011_00001_00010_0000000000000000 | 2,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 1);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sltiu_eq() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b001011_00001_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sltiu_gt() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 2,
            0b001011_00001_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sltiu_neg() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | -1_i16 as u16 as u32,
            0b001011_00001_00010_0000000000000000 | 1,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[2], 0);
    }

    #[test]
    #[wasm_bindgen_test]
    fn beq_eq() {
        let mut prog = le_byte_arr![0b000100_00000_00001_0000000000000000 | (12 >> 2)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4 + 12);
    }
    #[test]
    #[wasm_bindgen_test]
    fn beq_neq() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000100_00000_00001_0000000000000000 | (12 >> 2),
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8);
    }

    #[test]
    #[wasm_bindgen_test]
    fn bne_neq() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000101_00000_00001_0000000000000000 | (12 >> 2),
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8 + 12);
    }
    #[test]
    #[wasm_bindgen_test]
    fn bne_eq() {
        let mut prog = le_byte_arr![0b000101_00000_00001_0000000000000000 | (12 >> 2)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4);
    }

    #[test]
    #[wasm_bindgen_test]
    fn blez_zero() {
        let mut prog = le_byte_arr![0b000110_00000_00000_0000000000000000 | (12 >> 2)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4 + 12);
    }
    #[test]
    #[wasm_bindgen_test]
    fn blez_pos_one() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000110_00001_00000_0000000000000000 | (12 >> 2),
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8);
    }
    #[test]
    #[wasm_bindgen_test]
    fn blez_minus_one() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | (-1_i16 as u16 as u32),
            0b000110_00001_00000_0000000000000000 | (12 >> 2),
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8 + 12);
    }

    #[test]
    #[wasm_bindgen_test]
    fn bgtz_zero() {
        let mut prog = le_byte_arr![0b000111_00000_00000_0000000000000000 | (12 >> 2)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4);
    }
    #[test]
    #[wasm_bindgen_test]
    fn bgtz_one() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 1,
            0b000111_00001_00000_0000000000000000 | (12 >> 2),
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8 + 12);
    }

    #[test]
    #[wasm_bindgen_test]
    fn lb_pos() {
        let mut prog = le_byte_arr![
            0b100000_00000_00001_0000000000000101,
            0b00000000_00000000_00101101_00000000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 0b00101101);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lb_neg() {
        let mut prog = le_byte_arr![
            0b100000_00000_00001_0000000000000101,
            (-7_i8 as u8 as u32) << 8,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -7_i32 as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn lbu_pos() {
        let mut prog = le_byte_arr![
            0b100100_00000_00001_0000000000000101,
            0b00000000_00000000_00101101_00000000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 0b00101101);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lbu_neg() {
        let mut prog = le_byte_arr![
            0b100100_00000_00001_0000000000000101,
            (-7_i8 as u8 as u32) << 8,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -7_i8 as u8 as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sb() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 9185,
            0b101000_00000_00001_0000000000000011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(prog[3], (9185 & MASK8) as u8);
    }

    #[test]
    #[wasm_bindgen_test]
    fn lh_pos() {
        let mut prog = le_byte_arr![
            0b100001_00000_00001_0000000000000100,
            0b00000000_00000000_01001101_00101101,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 0b01001101_00101101);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lh_neg() {
        let mut prog = le_byte_arr![0b100001_00000_00001_0000000000000100, -7_i16 as u16 as u32,];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -7_i32 as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lh_misaligned() {
        let mut prog = le_byte_arr![0b100001_00000_00001_0000000000000101];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "misaligned load-half from 0b00000000000000000000000000000101",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::MisalignedLH(0b00000000000000000000000000000101)) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn lhu_pos() {
        let mut prog = le_byte_arr![
            0b100101_00000_00001_0000000000000100,
            0b00000000_00000000_01001101_00101101,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 0b01001101_00101101);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lhu_neg() {
        let mut prog = le_byte_arr![0b100101_00000_00001_0000000000000100, -7_i16 as u16 as u32,];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -7_i16 as u16 as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lhu_misaligned() {
        let mut prog = le_byte_arr![0b100101_00000_00001_0000000000000101];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "misaligned load-half from 0b00000000000000000000000000000101",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::MisalignedLH(0b00000000000000000000000000000101)) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn sh() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | 9185,
            0b101001_00000_00001_0000000000000010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(unsafe { prog.as_ref().index_aligned::<u16>(2) }, 9185);
    }
    #[test]
    #[wasm_bindgen_test]
    fn sh_misaligned() {
        let mut prog = le_byte_arr![0b101001_00000_00001_0000000000000011];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "misaligned save-half to 0b00000000000000000000000000000011",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::MisalignedSH(0b00000000000000000000000000000011)) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn lw_pos() {
        let mut prog = le_byte_arr![
            0b100011_00000_00001_0000000000000100,
            0b01010011_10011001_11001101_10101101,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 0b01010011_10011001_11001101_10101101);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lw_neg() {
        let mut prog = le_byte_arr![0b100011_00000_00001_0000000000000100, -7_i32 as u32,];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -7_i32 as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lw_misaligned() {
        let mut prog = le_byte_arr![0b100011_00000_00001_0000000000000010];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "misaligned load-word from 0b00000000000000000000000000000010",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::MisalignedLW(0b00000000000000000000000000000010)) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn sw() {
        let mut prog = le_byte_arr![
            0b001000_00000_00001_0000000000000000 | -9185_i16 as u16 as u32,
            0b101011_00000_00001_0000000000000100,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(
            unsafe { prog.as_ref().index_aligned::<u32>(4) },
            -9185_i32 as u32
        );
    }
    #[test]
    #[wasm_bindgen_test]
    fn sw_misaligned() {
        let mut prog = le_byte_arr![0b101011_00000_00001_0000000000010010];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) =>
                    v.as_string().unwrap()
                        == "misaligned save-word to 0b00000000000000000000000000010010",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::MisalignedSW(0b00000000000000000000000000010010)) => true,
                _ => false,
            })
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn syscall() {
        let mut prog = le_byte_arr![
            0b011010_00000000000000000000000000,
            0b000000_00010_00011_00100_00101_100000,
        ];
        let mut emu = Emulator::new();
        assert!(emu.step(&mut prog).unwrap());
        assert!(!emu.step(&mut prog).unwrap());
    }

    #[test]
    #[wasm_bindgen_test]
    fn invalid_funct() {
        let mut prog = le_byte_arr![0b000000_00000_00000_00000_00000_111111];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) => v.as_string().unwrap() == "invalid function 0b111111",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::InvalidFunction(0b111111)) => true,
                _ => false,
            });
        }
    }

    #[test]
    #[wasm_bindgen_test]
    fn invalid_opcode() {
        let mut prog = le_byte_arr![0b111111_00000_00000_00000_00000_000000];
        let mut emu = Emulator::new();
        #[cfg(target_arch = "wasm32")]
        {
            assert!(match emu.step(&mut prog) {
                Err(v) => v.as_string().unwrap() == "invalid opcode 0b111111",
                _ => false,
            });
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            assert!(match emu.step(&mut prog) {
                Err(ErrorType::InvalidOpcode(0b111111)) => true,
                _ => false,
            })
        }
    }
}

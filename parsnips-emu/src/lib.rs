#![no_std]
#![feature(unchecked_math, lang_items)]

// TODO: display more details about the sources of errors, i.e. opcodes and
// function codes, program counter value on overflow
#[cfg(target_arch = "wasm32")]
mod error {
    use core::{fmt, str::from_utf8_unchecked};
    use wasm_bindgen::JsValue;

    pub type ErrorType = JsValue;

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
            JsValue::from_str("overflow ocurred")
        };
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
        OutOfBounds { pc: u32, max: u32 },
        Overflow,
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
}

use error::*;

#[cfg(not(any(target_arch = "wasm32", test)))]
#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(not(any(target_arch = "wasm32", test)))]
use core::panic::PanicInfo;
#[cfg(not(any(target_arch = "wasm32", test)))]
#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}

mod inst;
use inst::{opcode::*, Inst};

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Emulator {
    regs: [u32; 32],
    // PERF: consider refactoring to a single u64
    lo: u32,
    hi: u32,
    pc: u32,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl Emulator {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new() -> Self {
        return Self {
            regs: [0; 32],
            lo: 0,
            hi: 0,
            pc: 0,
        };
    }

    pub fn get_reg(&self, reg: usize) -> u32 {
        self.regs[reg]
    }

    pub fn step(&mut self, memory: &mut [Inst]) -> Result<(), ErrorType> {
        use inst::InstFields;

        let inst_idx = (self.pc >> 2) as usize;
        if inst_idx >= memory.len() {
            return Err(ERR_OOB![self.pc, (memory.len() as u32 - 1) * 4]);
        }
        let inst = memory[inst_idx as usize];
        self.pc += 4;
        match inst.op() {
            REG => {
                use inst::function::*;
                use inst::RegFields;

                match inst.funct() {
                    // NOTE: the difference between ADD and ADDU is that ADD
                    // generates a trap when an overflow occurs
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
                            unsafe { self.regs[inst.rs()].unchecked_add(self.regs[inst.rt()]) };
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
                    MULT => {
                        use inst::DivMultFields;

                        let res =
                            self.regs[inst.rs()] as i32 as i64 * self.regs[inst.rt()] as i32 as i64;
                        self.hi = (res / (u32::MAX as i64 + 1)) as u32;
                        self.lo = (res % (u32::MAX as i64 + 1)) as u32;
                    }
                    MULTU => {
                        use inst::DivMultFields;

                        let res = self.regs[inst.rs()] as u64 * self.regs[inst.rt()] as u64;
                        self.hi = (res / (u32::MAX as u64 + 1)) as u32;
                        self.lo = (res % (u32::MAX as u64 + 1)) as u32;
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
                    _ => return Err(ERR_FUNCT![inst.funct()]),
                }
            }
            ADDI => {
                use inst::ArithLogIFields;

                // NOTE: casts back and forth ensure sign extension
                match (self.regs[inst.rs()] as i32).checked_add(inst.imm() as i16 as i32) {
                    Some(s) => self.regs[inst.rt()] = s as u32,
                    None => return Err(ERR_OVERFLOW![]),
                };
            }
            ADDIU => {
                use inst::ArithLogIFields;

                // NOTE: lack of casts back and forth ensure zero extension
                self.regs[inst.rt()] =
                    unsafe { self.regs[inst.rs()].unchecked_add(inst.imm() as u32) };
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
                    self.pc = (self.pc as i32 + inst.imm()) as u32;
                }
            }
            BNE => {
                use inst::BranchFields;

                if self.regs[inst.rs()] != self.regs[inst.rt()] {
                    self.pc = (self.pc as i32 + inst.imm()) as u32;
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
            SYSCALL | LB | LH | LW | LBU | LHU | SB | SH | SW => todo!(),
            _ => return Err(ERR_OP![inst.op()]),
        };

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::wasm_bindgen_test;

    // TODO: add tests to check for overflows once mults or shifts are
    // implemented

    #[test]
    #[wasm_bindgen_test]
    fn add_pos() {
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00011_0000000000000000 | (-1 as i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (-1 as i16 as u16 as u32),
            0b000000_00010_00011_00100_00101_100000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[4], -2 as i32 as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn add_big() {
        let mut prog = [
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
    fn addu_small() {
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (-11 as i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011000,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.lo, -44 as i32 as u32);
        assert_eq!(emu.hi, 0);
    }
    #[test]
    #[wasm_bindgen_test]
    fn mult_big() {
        // TODO: make these bigger when shifts are added
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (i16::MAX as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (i16::MAX as u16 as u32),
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (-1 as i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (-1 as i16 as u16 as u32),
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [0b011001_00000_00001_0000000000000000 | 17];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 17 << 16);
    }
    #[test]
    #[wasm_bindgen_test]
    fn lhi_then_llo() {
        let mut prog = [
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
        let mut prog = [0b011000_00000_00001_0000000000000000 | 17];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 17);
    }
    #[test]
    #[wasm_bindgen_test]
    fn llo_then_lhi() {
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b000000_00000_00001_00001_00011_000011,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], ((-2 as i32) << 1) as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn srav() {
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00010_00001_00001_00000_000111,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], ((-2 as i32) << 1) as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn srl() {
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b000000_00000_00001_00001_01111_000010,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], ((-2 as i32) << 4) as u32 >> 15);
    }

    #[test]
    #[wasm_bindgen_test]
    fn srlv() {
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 15,
            0b000000_00010_00001_00001_00000_000110,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], ((-2 as i32) << 4) as u32 >> 15);
    }

    #[test]
    #[wasm_bindgen_test]
    fn sub_pos() {
        let minuend = 159;
        let subtrahend = 61;
        let mut prog = [
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
        let minuend: i16 = -61;
        let subtrahend: i16 = -159;
        let mut prog = [
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
        let mut prog = [
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
        let minuend: i16 = -61;
        let subtrahend: i16 = -159;
        let mut prog = [
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
        let mut prog = [0b001000_00000_00001_0000000000000000 | (i16::MAX as u32)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], i16::MAX as u32);
    }
    #[test]
    #[wasm_bindgen_test]
    fn addi_neg() {
        let mut prog = [0b001000_00000_00001_0000000000000000 | (-1 as i16 as u16 as u32)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], -1 as i16 as i32 as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn addiu_small() {
        let mut prog = [0b001001_00000_00001_0000000000000000 | 7];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], 7);
    }
    #[test]
    #[wasm_bindgen_test]
    fn addiu_big() {
        let mut prog = [0b001001_00000_00001_0000000000000000 | (u16::MAX as u32)];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.regs[1], u16::MAX as u32);
    }

    #[test]
    #[wasm_bindgen_test]
    fn andi() {
        let mut prog = [
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
        let mut prog = [
            0b001000_00001_00001_0000000000000000 | 1,
            // jump negative 8 relative to what the PC would become, back to the
            // first instruction
            0b000010_11111111111111111111111000,
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
        let mut prog = [
            0b000010_00000000000000000010000000,
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
        let mut prog = [
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
    fn jal() {
        let mut prog = [
            0b001000_00001_00001_0000000000000000 | 1,
            // jump negative 8 relative to what the PC would become, back to the
            // first instruction
            0b000011_11111111111111111111111000,
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | -1 as i16 as u16 as u32,
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | -1 as i16 as u16 as u32,
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | -1 as i16 as u16 as u32,
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
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
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | -1 as i16 as u16 as u32,
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
        let mut prog = [0b000100_00000_00001_0000000000000000 | 12];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4 + 12);
    }
    #[test]
    #[wasm_bindgen_test]
    fn beq_neq() {
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | 1,
            0b000100_00000_00001_0000000000000000 | 12,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8);
    }

    #[test]
    #[wasm_bindgen_test]
    fn bne_neq() {
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | 1,
            0b000101_00000_00001_0000000000000000 | 12,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8 + 12);
    }
    #[test]
    #[wasm_bindgen_test]
    fn bne_eq() {
        let mut prog = [0b000101_00000_00001_0000000000000000 | 12];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4);
    }

    #[test]
    #[wasm_bindgen_test]
    fn blez_zero() {
        let mut prog = [0b000110_00000_00000_0000000000000000 | 12];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4 + 12);
    }
    #[test]
    #[wasm_bindgen_test]
    fn blez_pos_one() {
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | 1,
            0b000110_00001_00000_0000000000000000 | 12,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8);
    }
    #[test]
    #[wasm_bindgen_test]
    fn blez_minus_one() {
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | (-1 as i16 as u16 as u32),
            0b000110_00001_00000_0000000000000000 | 12,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8 + 12);
    }

    #[test]
    #[wasm_bindgen_test]
    fn bgtz_zero() {
        let mut prog = [0b000111_00000_00000_0000000000000000 | 12];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 4);
    }
    #[test]
    #[wasm_bindgen_test]
    fn bgtz_one() {
        let mut prog = [
            0b001000_00000_00001_0000000000000000 | 1,
            0b000111_00001_00000_0000000000000000 | 12,
        ];
        let mut emu = Emulator::new();
        emu.step(&mut prog).unwrap();
        emu.step(&mut prog).unwrap();
        assert_eq!(emu.pc, 8 + 12);
    }

    #[test]
    #[wasm_bindgen_test]
    fn invalid_funct() {
        let mut prog = [0b000000_00000_00000_00000_00000_111111];
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
        let mut prog = [0b111111_00000_00000_00000_00000_000000];
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

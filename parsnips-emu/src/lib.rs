#![feature(unchecked_math)]

mod inst;
use inst::{opcode::*, Inst};
use std::{error::Error, fmt};

#[derive(Debug)]
pub enum EmulatorError {
    Overflow,
    JumpOutOfRange { pc: u32, max: usize },
}
impl fmt::Display for EmulatorError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Overflow => write!(f, "overflow occurred"),
            Self::JumpOutOfRange { pc, max } => {
                write!(
                    f,
                    "jump out of range {} for program with max address {}",
                    pc, max
                )
            }
        }
    }
}
impl Error for EmulatorError {}

pub struct Emulator {
    registers: [u32; 32],
    lo: u32,
    hi: u32,
    // TODO: what are the possible values that need to be stored here?
    comparison_bit: bool,
    program: Vec<Inst>,
    program_counter: u32,
}

impl Emulator {
    pub const fn new(program: Vec<Inst>) -> Self {
        return Self {
            registers: [0; 32],
            lo: 0,
            hi: 0,
            comparison_bit: false,
            program,
            program_counter: 0,
        };
    }

    pub fn step(&mut self) -> Result<(), EmulatorError> {
        use inst::InstFields;

        let inst_idx = (self.program_counter >> 2) as usize;
        if inst_idx >= self.program.len() {
            return Err(EmulatorError::JumpOutOfRange {
                pc: self.program_counter,
                max: (self.program.len() << 2) - 4,
            });
        }
        let inst = &self.program[inst_idx];
        self.program_counter += 4;
        match inst.op() {
            REG => {
                use inst::function::*;
                use inst::RegFields;

                match inst.funct() {
                    // NOTE: the difference between ADD and ADDU is that ADD
                    // generates a trap when an overflow occurs
                    ADD => {
                        use inst::ArithLogFields;

                        match (self.registers[inst.rs()] as i32)
                            .checked_add(self.registers[inst.rt()] as i32)
                        {
                            Some(s) => self.registers[inst.rd()] = s as u32,
                            None => return Err(EmulatorError::Overflow),
                        };
                    }
                    ADDU => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd()] = unsafe {
                            self.registers[inst.rs()].unchecked_add(self.registers[inst.rt()])
                        };
                    }
                    AND => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd()] =
                            self.registers[inst.rs()] & self.registers[inst.rt()];
                    }
                    DIV => {
                        use inst::DivMultFields;

                        self.lo = (self.registers[inst.rs()] as i32
                            / self.registers[inst.rt()] as i32)
                            as u32;
                        self.hi = (self.registers[inst.rs()] as i32
                            % self.registers[inst.rt()] as i32)
                            as u32;
                    }
                    DIVU => {
                        use inst::DivMultFields;

                        self.lo = self.registers[inst.rs()] / self.registers[inst.rt()];
                        self.hi = self.registers[inst.rs()] % self.registers[inst.rt()];
                    }
                    MULT => {
                        use inst::DivMultFields;

                        let res = self.registers[inst.rs()] as i32 as i64
                            * self.registers[inst.rt()] as i32 as i64;
                        self.hi = (res / (u32::MAX as i64 + 1)) as u32;
                        self.lo = (res % (u32::MAX as i64 + 1)) as u32;
                    }
                    MULTU => {
                        use inst::DivMultFields;

                        let res =
                            self.registers[inst.rs()] as u64 * self.registers[inst.rt()] as u64;
                        self.hi = (res / (u32::MAX as u64 + 1)) as u32;
                        self.lo = (res % (u32::MAX as u64 + 1)) as u32;
                    }
                    NOR => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd()] =
                            !(self.registers[inst.rs()] | self.registers[inst.rt()]);
                    }
                    OR => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd()] =
                            self.registers[inst.rs()] | self.registers[inst.rt()];
                    }
                    XOR => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd()] =
                            self.registers[inst.rs()] ^ self.registers[inst.rt()];
                    }
                    MFHI => {
                        use inst::MoveFromFields;

                        self.registers[inst.rd()] = self.hi;
                    }
                    MFLO => {
                        use inst::MoveFromFields;

                        self.registers[inst.rd()] = self.lo;
                    }
                    MTHI => {
                        use inst::MoveToFields;

                        self.hi = self.registers[inst.rs()];
                    }
                    MTLO => {
                        use inst::MoveToFields;

                        self.lo = self.registers[inst.rs()];
                    }
                    SLL => {
                        use inst::ShiftFields;

                        self.registers[inst.rd()] = self.registers[inst.rt()] << inst.shamt();
                    }
                    SLLV => {
                        use inst::ShiftVFields;

                        self.registers[inst.rd()] =
                            self.registers[inst.rt()] << self.registers[inst.rs()];
                    }
                    SRA => {
                        use inst::ShiftFields;

                        self.registers[inst.rd()] =
                            (self.registers[inst.rt()] as i32 >> inst.shamt()) as u32;
                    }
                    SRAV => {
                        use inst::ShiftVFields;

                        self.registers[inst.rd()] =
                            (self.registers[inst.rt()] as i32 >> self.registers[inst.rs()]) as u32;
                    }
                    SRL => {
                        use inst::ShiftFields;

                        self.registers[inst.rd()] = self.registers[inst.rt()] >> inst.shamt();
                    }
                    SRLV => {
                        use inst::ShiftVFields;

                        self.registers[inst.rd()] =
                            self.registers[inst.rt()] >> self.registers[inst.rs()];
                    }
                    _ => todo!(),
                }
            }
            ADDI => {
                use inst::ArithLogIFields;

                // NOTE: casts back and forth ensure sign extension
                match (self.registers[inst.rs()] as i32).checked_add(inst.imm() as i16 as i32) {
                    Some(s) => self.registers[inst.rt()] = s as u32,
                    None => return Err(EmulatorError::Overflow),
                };
            }
            ADDIU => {
                use inst::ArithLogIFields;

                // NOTE: lack of casts back and forth ensure zero extension
                self.registers[inst.rt()] =
                    unsafe { self.registers[inst.rs()].unchecked_add(inst.imm() as u32) };
            }
            ANDI => {
                use inst::ArithLogIFields;

                self.registers[inst.rt()] = self.registers[inst.rs()] & inst.imm() as u32;
            }
            ORI => {
                use inst::ArithLogIFields;

                self.registers[inst.rt()] = self.registers[inst.rs()] | inst.imm() as u32;
            }
            XORI => {
                use inst::ArithLogIFields;

                self.registers[inst.rt()] = self.registers[inst.rs()] ^ inst.imm() as u32;
            }
            // PERF: figure out if unsafe and pointer hyjinks can speed LHI and LLO up
            LHI => {
                use inst::LoadIFields;

                self.registers[inst.rt()] &= u16::MAX as u32;
                self.registers[inst.rt()] |= (inst.imm() as u32) << 16;
            }
            LLO => {
                use inst::LoadIFields;

                self.registers[inst.rt()] &= (u16::MAX as u32) << 16;
                self.registers[inst.rt()] |= inst.imm() as u32;
            }
            J => {
                use inst::JumpFields;

                self.program_counter = (self.program_counter as i32 + inst.imm()) as u32;
            }
            _ => todo!(),
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;

    type RUE = Result<(), Box<dyn Error>>;

    macro_rules! step_with {
        ( $( $x:expr ),* ) => {
            {
                let mut emu = Emulator::new(vec![$(
                    $x,
                )*]);
                $(
                    $x;
                    emu.step()?;
                )*
                emu
            }
        };
    }

    // TODO: add tests to check for overflows once mults or shifts are
    // implemented

    #[test]
    fn add_pos() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00011_0000000000000000 | 2,
            0b001000_00000_00010_0000000000000000 | 1,
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], 3);
        Ok(())
    }
    #[test]
    fn add_neg() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00011_0000000000000000 | (-1 as i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (-1 as i16 as u16 as u32),
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], -2 as i32 as u32);
        Ok(())
    }
    #[test]
    fn add_big() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00011_0000000000000000 | (i16::MAX as u32),
            0b001000_00000_00010_0000000000000000 | (i16::MAX as u32),
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], u16::MAX as u32 - 1);
        Ok(())
    }

    #[test]
    fn addu_small() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001001_00000_00011_0000000000000000 | 2,
            0b001001_00000_00010_0000000000000000 | 1,
            0b000000_00010_00011_00100_00101_100001
        ];
        assert_eq!(emu.registers[4], 3);
        Ok(())
    }
    #[test]
    fn addu_big() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001001_00000_00011_0000000000000000 | (u16::MAX as u32),
            0b001001_00000_00010_0000000000000000 | (u16::MAX as u32),
            0b000000_00010_00011_00100_00101_100001
        ];
        assert_eq!(emu.registers[4], u16::MAX as u32 * 2);
        Ok(())
    }

    #[test]
    fn and() -> RUE {
        let emu = step_with![
            0b001001_00000_00011_1000001101101001,
            0b001001_00000_00010_1011000100111011,
            0b000000_00010_00011_00100_00101_100100
        ];
        assert_eq!(emu.registers[4], 0b1000000100101001);
        Ok(())
    }

    // TODO: add tests that highlight the difference between div and divu

    #[test]
    fn div() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 11,
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011010
        ];
        assert_eq!(emu.lo, 2);
        assert_eq!(emu.hi, 3);
        Ok(())
    }

    #[test]
    fn divu() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 11,
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011011
        ];
        assert_eq!(emu.lo, 2);
        assert_eq!(emu.hi, 3);
        Ok(())
    }

    #[test]
    fn mult_pos() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 11,
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011000
        ];
        assert_eq!(emu.lo, 44);
        assert_eq!(emu.hi, 0);
        Ok(())
    }
    #[test]
    fn mult_neg() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (-11 as i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 4,
            0b000000_00001_00010_0000000000_011000
        ];
        assert_eq!(emu.lo, -44 as i32 as u32);
        assert_eq!(emu.hi, 0);
        Ok(())
    }
    #[test]
    fn mult_big() -> RUE {
        // TODO: make these bigger when shifts are added
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (i16::MAX as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (i16::MAX as u16 as u32),
            0b000000_00001_00010_0000000000_011000
        ];
        assert_eq!(emu.lo, i16::MAX as u32 * i16::MAX as u32);
        assert_eq!(emu.hi, 0);
        Ok(())
    }

    #[test]
    fn multu_small() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 7,
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00001_00010_0000000000_011001
        ];
        assert_eq!(emu.lo, 21);
        assert_eq!(emu.hi, 0);
        Ok(())
    }

    #[test]
    fn multu_big() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (-1 as i16 as u16 as u32),
            0b001000_00000_00010_0000000000000000 | (-1 as i16 as u16 as u32),
            0b000000_00001_00010_0000000000_011001
        ];
        assert_eq!(emu.lo, 1);
        assert_eq!(emu.hi, 4294967294);
        Ok(())
    }

    #[test]
    fn nor() -> RUE {
        let emu = step_with![
            0b001000_00000_00001_1100000100001101,
            0b001001_00000_00010_1010101000101100,
            0b000000_00001_00010_00011_00000_100111
        ];
        assert_eq!(emu.registers[3], 0b0001010011010010);
        Ok(())
    }

    #[test]
    fn or() -> RUE {
        let emu = step_with![
            0b001001_00000_00001_1100000100001101,
            0b001001_00000_00010_1010101000101100,
            0b000000_00001_00010_00011_00000_100101
        ];
        assert_eq!(emu.registers[3], 0b1110101100101101);
        Ok(())
    }

    #[test]
    fn ori() -> RUE {
        let emu = step_with![
            0b001001_00000_00001_1100000100001101,
            0b001101_00001_00010_1010101000101100
        ];
        assert_eq!(emu.registers[2], 0b1110101100101101);
        Ok(())
    }

    #[test]
    fn xor() -> RUE {
        let emu = step_with![
            0b001001_00000_00001_1100000100001101,
            0b001001_00000_00010_1010101000101100,
            0b000000_00001_00010_00011_00000_100110
        ];
        assert_eq!(emu.registers[3], 0b0110101100100001);
        Ok(())
    }

    #[test]
    fn xori() -> RUE {
        let emu = step_with![
            0b001001_00000_00001_1100000100001101,
            0b001110_00001_00010_1010101000101100
        ];
        assert_eq!(emu.registers[2], 0b0110101100100001);
        Ok(())
    }

    #[test]
    fn lhi() -> RUE {
        #[allow(unused)]
        let emu = step_with![0b011001_00000_00001_0000000000000000 | 17];
        assert_eq!(emu.registers[1], 17 << 16);
        Ok(())
    }
    #[test]
    fn lhi_then_llo() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b011001_00000_00001_0000000000000000 | 17,
            0b011000_00000_00001_0000000000000000 | 17
        ];
        assert_eq!(emu.registers[1], (17 << 16) + 17);
        Ok(())
    }

    #[test]
    fn llo() -> RUE {
        #[allow(unused)]
        let emu = step_with![0b011000_00000_00001_0000000000000000 | 17];
        assert_eq!(emu.registers[1], 17);
        Ok(())
    }
    #[test]
    fn llo_then_lhi() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b011000_00000_00001_0000000000000000 | 17,
            0b011001_00000_00001_0000000000000000 | 17
        ];
        assert_eq!(emu.registers[1], (17 << 16) + 17);
        Ok(())
    }

    #[test]
    fn mtfhi() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 31,
            0b000000_00001_00000_00000_00000_010001,
            0b000000_00000_00000_00010_00000_010000
        ];
        assert_eq!(emu.hi, 31);
        assert_eq!(emu.registers[2], 31);
        Ok(())
    }

    #[test]
    fn mtflo() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 31,
            0b000000_00001_00000_00000_00000_010011,
            0b000000_00000_00000_00010_00000_010010
        ];
        assert_eq!(emu.lo, 31);
        assert_eq!(emu.registers[2], 31);
        Ok(())
    }

    #[test]
    fn sll() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 31,
            0b000000_00000_00001_00001_00111_000000
        ];
        assert_eq!(emu.registers[1], 31 << 7);
        Ok(())
    }

    #[test]
    fn sllv() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | 31,
            0b001000_00000_00010_0000000000000000 | 7,
            0b000000_00010_00001_00001_00000_000100
        ];
        assert_eq!(emu.registers[1], 31 << 7);
        Ok(())
    }

    #[test]
    fn sra() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b000000_00000_00001_00001_00011_000011
        ];
        assert_eq!(emu.registers[1], ((-2 as i32) << 1) as u32);
        Ok(())
    }

    #[test]
    fn srav() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00010_00001_00001_00000_000111
        ];
        assert_eq!(emu.registers[1], ((-2 as i32) << 1) as u32);
        Ok(())
    }

    #[test]
    fn srl() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (31 << 6),
            0b000000_00000_00001_00001_00011_000010
        ];
        assert_eq!(emu.registers[1], 31 << 3);
        Ok(())
    }
    #[test]
    fn srl_not_extended() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b000000_00000_00001_00001_01111_000010
        ];
        assert_eq!(emu.registers[1], ((-2 as i32) << 4) as u32 >> 15);
        Ok(())
    }

    #[test]
    fn srlv() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (31 << 6),
            0b001000_00000_00010_0000000000000000 | 3,
            0b000000_00010_00001_00001_00000_000110
        ];
        assert_eq!(emu.registers[1], 31 << 3);
        Ok(())
    }
    #[test]
    fn srlv_not_extended() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00000_00001_0000000000000000 | (((-2 as i16) << 4) as u16 as u32),
            0b001000_00000_00010_0000000000000000 | 15,
            0b000000_00010_00001_00001_00000_000110
        ];
        assert_eq!(emu.registers[1], ((-2 as i32) << 4) as u32 >> 15);
        Ok(())
    }

    #[test]
    fn addi_pos() -> RUE {
        #[allow(unused)]
        let emu = step_with![0b001000_00000_00001_0000000000000000 | (i16::MAX as u32)];
        assert_eq!(emu.registers[1], i16::MAX as u32);
        Ok(())
    }
    #[test]
    fn addi_neg() -> RUE {
        #[allow(unused)]
        let emu = step_with![0b001000_00000_00001_0000000000000000 | (-1 as i16 as u16 as u32)];
        assert_eq!(emu.registers[1], -1 as i16 as i32 as u32);
        Ok(())
    }

    #[test]
    fn addiu_small() -> RUE {
        #[allow(unused)]
        let emu = step_with![0b001001_00000_00001_0000000000000000 | 7];
        assert_eq!(emu.registers[1], 7);
        Ok(())
    }
    #[test]
    fn addiu_big() -> RUE {
        #[allow(unused)]
        let emu = step_with![0b001001_00000_00001_0000000000000000 | (u16::MAX as u32)];
        assert_eq!(emu.registers[1], u16::MAX as u32);
        Ok(())
    }

    #[test]
    fn andi() -> RUE {
        let emu = step_with![
            0b001001_00000_00001_1000001101101001,
            0b001100_00001_00010_1011000100111011
        ];
        assert_eq!(emu.registers[2], 0b1000000100101001);
        Ok(())
    }

    #[test]
    fn j() -> RUE {
        #[allow(unused)]
        let emu = step_with![
            0b001000_00001_00001_0000000000000000 | 1,
            // jump negative 8 relative to what the PC would become, back to the
            // first instruction
            0b000010_11111111111111111111111000,
            0b001000_00000_00010_0000000000000000 | 1
        ];
        assert_eq!(emu.registers[1], 2);
        assert_eq!(emu.registers[2], 0);
        Ok(())
    }
    #[test]
    fn j_outofrange() -> RUE {
        let mut emu = Emulator::new(vec![
            0b000010_00000000000000000010000000,
            0b000000_00000_00000_0000000000000000,
        ]);
        emu.step()?;
        assert!(match emu.step() {
            Err(EmulatorError::JumpOutOfRange { pc: 132, max: 4 }) => true,
            _ => false,
        });
        Ok(())
    }
}

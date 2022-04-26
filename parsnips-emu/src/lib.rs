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
    // TODO: what are the possible values that need to be stored here?
    comparison_bit: bool,
    program: Vec<Inst>,
    program_counter: u32,
}

impl Emulator {
    pub const fn new(program: Vec<Inst>) -> Self {
        return Self {
            registers: [0; 32],
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
                        }
                    }
                    ADDU => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd()] = unsafe {
                            self.registers[inst.rs()].unchecked_add(self.registers[inst.rt()])
                        }
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
                }
            }
            ADDIU => {
                use inst::ArithLogIFields;

                // NOTE: lack of casts back and forth ensure zero extension
                self.registers[inst.rt()] =
                    unsafe { self.registers[inst.rs()].unchecked_add(inst.imm() as u32) };
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

    // TODO: add tests to check for overflows

    #[test]
    fn addi_pos() -> RUE {
        let emu = step_with![0b001000_00000_00001_0111111111111111];
        assert_eq!(emu.registers[1], i16::max_value() as u32);
        Ok(())
    }

    #[test]
    fn addi_neg() -> RUE {
        let emu = step_with![0b001000_00000_00001_1111111111111111];
        assert_eq!(emu.registers[1], -1 as i16 as i32 as u32);
        Ok(())
    }

    #[test]
    fn add_pos() -> RUE {
        let emu = step_with![
            0b001000_00000_00011_0000000000000010,
            0b001000_00000_00010_0000000000000001,
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], 3);
        Ok(())
    }

    #[test]
    fn add_neg() -> RUE {
        let emu = step_with![
            0b001000_00000_00011_1111111111111111,
            0b001000_00000_00010_1111111111111111,
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], -2 as i32 as u32);
        Ok(())
    }

    #[test]
    fn j() -> RUE {
        let emu = step_with![
            0b001000_00001_00001_0000000000000001,
            // jump negative 8 relative to what the PC would become, back to the
            // first instruction
            0b000010_11111111111111111111111000,
            0b001000_00000_00010_0000000000000001
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

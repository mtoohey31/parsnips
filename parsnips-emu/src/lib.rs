#![feature(unchecked_math)]

mod inst;
use inst::{opcode::*, Inst};
use std::{error::Error, fmt};

#[derive(Debug)]
pub enum EmulatorError {
    Overflow,
}
impl fmt::Display for EmulatorError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "overflow occurred")
    }
}
impl Error for EmulatorError {}

pub struct Emulator {
    registers: [u32; 32],
    // TODO: what are the possible values that need to be stored here?
    comparison_bit: bool,
    program: Vec<Inst>,
    program_counter: usize,
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

        let inst = &self.program[self.program_counter];
        self.program_counter += 1;
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
}

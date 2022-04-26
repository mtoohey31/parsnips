#![feature(unchecked_math)]

mod inst;
use inst::{opcode::*, Inst};

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

    pub fn step(&mut self) {
        use inst::InstFields;

        let inst = &self.program[self.program_counter];
        self.program_counter += 1;
        match inst.op() {
            REG => {
                use inst::function::*;
                use inst::RegFields;

                match inst.funct() {
                    ADD => {
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

                self.registers[inst.rt()] =
                    self.registers[inst.rs()] + inst.imm() as i16 as i32 as u32;
            }
            _ => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! step_with {
        ( $( $x:expr ),* ) => {
            {
                let mut emu = Emulator::new(vec![$(
                    $x,
                )*]);
                $(
                    $x;
                    emu.step();
                )*
                emu
            }
        };
    }

    #[test]
    fn addi_pos() {
        let emu = step_with![0b001000_00000_00001_0111111111111111];
        assert_eq!(emu.registers[1], i16::max_value() as u32);
    }

    #[test]
    fn addi_neg() {
        let emu = step_with![0b001000_00000_00001_1111111111111111];
        assert_eq!(emu.registers[1], -1 as i16 as i32 as u32);
    }

    #[test]
    fn add_pos() {
        let emu = step_with![
            0b001000_00000_00011_0000000000000010,
            0b001000_00000_00010_0000000000000001,
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], 3);
    }

    #[test]
    fn add_neg() {
        let emu = step_with![
            0b001000_00000_00011_1111111111111111,
            0b001000_00000_00010_1111111111111111,
            0b000000_00010_00011_00100_00101_100000
        ];
        assert_eq!(emu.registers[4], -2 as i32 as u32);
    }
}

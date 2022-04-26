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
        println!("{:#08b}", inst.op());
        match inst.op() {
            REG => {
                use inst::function::*;
                use inst::RegFields;

                match inst.funct() {
                    ADD => {
                        use inst::ArithLogFields;

                        self.registers[inst.rd() as usize] =
                            self.registers[inst.rs() as usize] + self.registers[inst.rt() as usize];
                    }
                    _ => todo!(),
                }
            }
            _ => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut emu = Emulator::new(vec![0b000000_00010_00011_00100_00101_100000]);
        emu.step();
        assert_eq!(emu.registers[4], 0);
    }
}

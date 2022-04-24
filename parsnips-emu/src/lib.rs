use ux::*;

#[repr(packed)]
pub struct Inst(u6);

const R_INST: Inst = Inst(ux::u6::new(0b00001000u8));


pub struct Instruction {
    opcode: u5,
    data: u27,
}

pub struct Emulator {
    registers: [u32; 32],
    // cmp_flags: ???,
    program: Vec<Instruction>,
}



#[cfg(test)]
mod tests {
    use ux::*;
    use super::*;
    use std::mem::size_of;

    #[repr(packed)]
    struct oool{
        type1: u2, 
        type2: u6
    
    }
    

    #[test]
    fn it_takes_32_bytes() {
        assert_eq!(size_of::<oool>(), 1)
    }

    
}
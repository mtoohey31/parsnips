// source: https://student.cs.uwaterloo.ca/~isg/res/mips/opcodes
// TODO: figure out how to make this less boilerplatey, maybe with a proceedural
// macro?

pub mod function;
pub mod opcode;

const MASK5: u32 = (1 << 5) - 1;
const MASK6: u32 = (1 << 6) - 1;
const MASK16: u32 = (1 << 16) - 1;
const MASK26: u32 = (1 << 26) - 1;

pub type Inst = u32;
pub trait InstFields {
    fn op(&self) -> u8;
}
impl InstFields for Inst {
    #[inline(always)]
    fn op(&self) -> u8 {
        (self >> 26) as u8
    }
}

// register encodings

pub trait RegFields {
    fn funct(&self) -> u8;
}
impl RegFields for Inst {
    #[inline(always)]
    fn funct(&self) -> u8 {
        (self & MASK6) as u8
    }
}

pub trait ArithLogFields {
    fn rs(&self) -> u8;
    fn rt(&self) -> u8;
    fn rd(&self) -> u8;
}
impl ArithLogFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn rd(&self) -> u8 {
        (self >> 11 & MASK5) as u8
    }
}

pub trait DivMultFields {
    fn rs(&self) -> u8;
    fn rt(&self) -> u8;
}
impl DivMultFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
}

pub trait ShiftFields {
    fn rt(&self) -> u8;
    fn rd(&self) -> u8;
    fn shamt(&self) -> u8;
}
impl ShiftFields for Inst {
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn rd(&self) -> u8 {
        (self >> 11 & MASK5) as u8
    }
    #[inline(always)]
    fn shamt(&self) -> u8 {
        (self >> 6 & MASK5) as u8
    }
}

pub trait ShiftVFields {
    fn rs(&self) -> u8;
    fn rt(&self) -> u8;
    fn rd(&self) -> u8;
}
impl ShiftVFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn rd(&self) -> u8 {
        (self >> 11 & MASK5) as u8
    }
}

pub trait JumpRFields {
    fn rs(&self) -> u8;
}
impl JumpRFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
}

pub trait MoveFromFields {
    fn rd(&self) -> u8;
}
impl MoveFromFields for Inst {
    #[inline(always)]
    fn rd(&self) -> u8 {
        (self >> 11 & MASK5) as u8
    }
}

pub trait MoveToFields {
    fn rs(&self) -> u8;
}
impl MoveToFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
}

// immediate encodings

pub trait ArithLogIFields {
    fn rt(&self) -> u8;
    fn rs(&self) -> u8;
    fn imm(&self) -> u16;
}
impl ArithLogIFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn imm(&self) -> u16 {
        (self & MASK16) as u16
    }
}

pub trait LoadIFields {
    fn rt(&self) -> u8;
    fn imm(&self) -> u16;
}
impl LoadIFields for Inst {
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn imm(&self) -> u16 {
        (self & MASK16) as u16
    }
}

pub trait BranchFields {
    fn rs(&self) -> u8;
    fn rt(&self) -> u8;
    fn label(&self, curr: u32) -> u32;
}
impl BranchFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn label(&self, curr: u32) -> u32 {
        (self & MASK16 - (curr + 4)) >> 2
    }
}

pub trait BranchZFields {
    fn rs(&self) -> u8;
    fn label(&self, curr: u32) -> u32;
}
impl BranchZFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn label(&self, curr: u32) -> u32 {
        (self & MASK16 - (curr + 4)) >> 2
    }
}

pub trait LoadStoreFields {
    fn rt(&self) -> u8;
    fn rs(&self) -> u8;
    fn imm(&self) -> u16;
}
impl LoadStoreFields for Inst {
    #[inline(always)]
    fn rs(&self) -> u8 {
        (self >> 21 & MASK5) as u8
    }
    #[inline(always)]
    fn rt(&self) -> u8 {
        (self >> 16 & MASK5) as u8
    }
    #[inline(always)]
    fn imm(&self) -> u16 {
        (self & MASK16) as u16
    }
}

// jump encodings

pub trait JumpFields {
    fn label(&self, curr: u32) -> u32;
}
impl JumpFields for Inst {
    #[inline(always)]
    fn label(&self, curr: u32) -> u32 {
        (self & MASK26 - (curr + 4)) >> 2
    }
}

pub trait TrapFields {
    fn imm(&self) -> u32;
}
impl TrapFields for Inst {
    #[inline(always)]
    fn imm(&self) -> u32 {
        self & MASK26
    }
}

// TODO: write tests for all traits to verify that they get the right fields

#[cfg(test)]
mod tests {
    use super::Inst;

    const REG_INST: Inst = 0b000001_00010_00011_00100_00101_000110;

    #[test]
    fn opfields() {
        use super::InstFields;

        assert_eq!(REG_INST.op(), 1);
    }

    #[test]
    fn reg_fields() {
        use super::RegFields;

        assert_eq!(REG_INST.funct(), 6);
    }
}

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
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
    fn rd(&self) -> usize;
}
impl ArithLogFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn rd(&self) -> usize {
        (self >> 11 & MASK5) as usize
    }
}

pub trait DivMultFields {
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
}
impl DivMultFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
}

pub trait ShiftFields {
    fn rt(&self) -> usize;
    fn rd(&self) -> usize;
    fn shamt(&self) -> u8;
}
impl ShiftFields for Inst {
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn rd(&self) -> usize {
        (self >> 11 & MASK5) as usize
    }
    #[inline(always)]
    fn shamt(&self) -> u8 {
        (self >> 6 & MASK5) as u8
    }
}

pub trait ShiftVFields {
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
    fn rd(&self) -> usize;
}
impl ShiftVFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn rd(&self) -> usize {
        (self >> 11 & MASK5) as usize
    }
}

pub trait JumpRFields {
    fn rs(&self) -> usize;
}
impl JumpRFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
}

pub trait MoveFromFields {
    fn rd(&self) -> usize;
}
impl MoveFromFields for Inst {
    #[inline(always)]
    fn rd(&self) -> usize {
        (self >> 11 & MASK5) as usize
    }
}

pub trait MoveToFields {
    fn rs(&self) -> usize;
}
impl MoveToFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
}

// immediate encodings

pub trait ArithLogIFields {
    fn rt(&self) -> usize;
    fn rs(&self) -> usize;
    fn imm(&self) -> u16;
}
impl ArithLogIFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn imm(&self) -> u16 {
        (self & MASK16) as u16
    }
}

pub trait LoadIFields {
    fn rt(&self) -> usize;
    fn imm(&self) -> u16;
}
impl LoadIFields for Inst {
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn imm(&self) -> u16 {
        (self & MASK16) as u16
    }
}

pub trait BranchFields {
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
    fn imm(&self) -> i32;
}
impl BranchFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn imm(&self) -> i32 {
        (self & MASK16) as i16 as i32
    }
}

pub trait BranchZFields {
    fn rs(&self) -> usize;
    fn imm(&self) -> i32;
}
impl BranchZFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn imm(&self) -> i32 {
        (self & MASK16) as i16 as i32
    }
}

pub trait LoadStoreFields {
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
    fn imm(&self) -> i32;
}
impl LoadStoreFields for Inst {
    #[inline(always)]
    fn rs(&self) -> usize {
        (self >> 21 & MASK5) as usize
    }
    #[inline(always)]
    fn rt(&self) -> usize {
        (self >> 16 & MASK5) as usize
    }
    #[inline(always)]
    fn imm(&self) -> i32 {
        (self & MASK16) as i16 as i32
    }
}

// jump encodings

pub trait JumpFields {
    fn imm(&self) -> i32;
}
impl JumpFields for Inst {
    #[inline(always)]
    fn imm(&self) -> i32 {
        ((self & MASK26) << 6) as i32 >> 6
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
    use wasm_bindgen_test::wasm_bindgen_test;

    const REG_INST: Inst = 0b000001_00010_00011_00100_00101_000110;

    #[test]
    #[wasm_bindgen_test]
    fn opfields() {
        use super::InstFields;

        assert_eq!(REG_INST.op(), 1);
    }

    #[test]
    #[wasm_bindgen_test]
    fn reg_fields() {
        use super::RegFields;

        assert_eq!(REG_INST.funct(), 6);
    }
}

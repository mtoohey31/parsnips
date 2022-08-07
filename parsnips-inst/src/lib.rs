#![no_std]

mod function;
mod opcode;
pub use function::Funct;
pub use opcode::Op;

const MASK5: u32 = (1 << 5) - 1;
const MASK6: u32 = (1 << 6) - 1;
const MASK16: u32 = (1 << 16) - 1;
const MASK26: u32 = (1 << 26) - 1;

// source: https://student.cs.uwaterloo.ca/~isg/res/mips/opcodes

pub type Inst = u32;
pub trait InstFields {
    unsafe fn op(&self) -> Op;
}
impl InstFields for Inst {
    #[inline(always)]
    unsafe fn op(&self) -> Op {
        Op::from_unchecked((self >> 26) as u8)
    }
}

// register encodings

pub trait RegFields {
    unsafe fn funct(&self) -> Funct;
}
impl RegFields for Inst {
    #[inline(always)]
    unsafe fn funct(&self) -> Funct {
        Funct::from_unchecked((self & MASK6) as u8)
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

use num_enum::{IntoPrimitive, TryFromPrimitive};
use strum_macros::EnumString;

#[cfg_attr(test, derive(Debug))]
#[derive(Eq, PartialEq, TryFromPrimitive, IntoPrimitive, EnumString)]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
pub enum Op {
    REG = 0b000000,
    J = 0b000010,
    JAL = 0b000011,
    BEQ = 0b000100,
    BNE = 0b000101,
    BLEZ = 0b000110,
    BGTZ = 0b000111,
    ADDI = 0b001000,
    ADDIU = 0b001001,
    SLTI = 0b001010,
    SLTIU = 0b001011,
    ANDI = 0b001100,
    ORI = 0b001101,
    XORI = 0b001110,
    LLO = 0b011000,
    LHI = 0b011001,
    SYSCALL = 0b011010,
    LB = 0b100000,
    LH = 0b100001,
    LW = 0b100011,
    LBU = 0b100100,
    LHU = 0b100101,
    SB = 0b101000,
    SH = 0b101001,
    SW = 0b101011,
}

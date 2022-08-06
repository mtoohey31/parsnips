use num_enum::{IntoPrimitive, TryFromPrimitive};
use strum_macros::EnumString;

#[cfg_attr(test, derive(Debug))]
#[derive(Eq, PartialEq, TryFromPrimitive, IntoPrimitive, EnumString)]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
pub enum Funct {
    SLL = 0b000000,
    SRL = 0b000010,
    SRA = 0b000011,
    SLLV = 0b000100,
    SRLV = 0b000110,
    SRAV = 0b000111,
    JR = 0b001000,
    JALR = 0b001001,
    MFHI = 0b010000,
    MTHI = 0b010001,
    MFLO = 0b010010,
    MTLO = 0b010011,
    MULT = 0b011000,
    MULTU = 0b011001,
    DIV = 0b011010,
    DIVU = 0b011011,
    ADD = 0b100000,
    ADDU = 0b100001,
    SUB = 0b100010,
    SUBU = 0b100011,
    AND = 0b100100,
    OR = 0b100101,
    XOR = 0b100110,
    NOR = 0b100111,
    SLT = 0b101010,
    SLTU = 0b101001,
}

use strum_macros::EnumString;

pub const SLL: u8 = 0b000000;
pub const SRL: u8 = 0b000010;
pub const SRA: u8 = 0b000011;
pub const SLLV: u8 = 0b000100;
pub const SRLV: u8 = 0b000110;
pub const SRAV: u8 = 0b000111;
pub const JR: u8 = 0b001000;
pub const JALR: u8 = 0b001001;
pub const MFHI: u8 = 0b010000;
pub const MTHI: u8 = 0b010001;
pub const MFLO: u8 = 0b010010;
pub const MTLO: u8 = 0b010011;
pub const MULT: u8 = 0b011000;
pub const MULTU: u8 = 0b011001;
pub const DIV: u8 = 0b011010;
pub const DIVU: u8 = 0b011011;
pub const ADD: u8 = 0b100000;
pub const ADDU: u8 = 0b100001;
pub const SUB: u8 = 0b100010;
pub const SUBU: u8 = 0b100011;
pub const AND: u8 = 0b100100;
pub const OR: u8 = 0b100101;
pub const XOR: u8 = 0b100110;
pub const NOR: u8 = 0b100111;
pub const SLT: u8 = 0b101010;
pub const SLTU: u8 = 0b101001;

#[derive(Debug, EnumString)]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
pub enum Funct {
    SLL = SLL,
    SRL = SRL,
    SRA = SRA,
    SLLV = SLLV,
    SRLV = SRLV,
    SRAV = SRAV,
    JR = JR,
    JALR = JALR,
    MFHI = MFHI,
    MTHI = MTHI,
    MFLO = MFLO,
    MTLO = MTLO,
    MULT = MULT,
    MULTU = MULTU,
    DIV = DIV,
    DIVU = DIVU,
    ADD = ADD,
    ADDU = ADDU,
    SUB = SUB,
    SUBU = SUBU,
    AND = AND,
    OR = OR,
    XOR = XOR,
    NOR = NOR,
    SLT = SLT,
    SLTU = SLTU,
}

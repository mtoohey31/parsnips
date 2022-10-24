use strum_macros::EnumString;

pub const REG: u8 = 0b000000;
pub const J: u8 = 0b000010;
pub const JAL: u8 = 0b000011;
pub const BEQ: u8 = 0b000100;
pub const BNE: u8 = 0b000101;
pub const BLEZ: u8 = 0b000110;
pub const BGTZ: u8 = 0b000111;
pub const ADDI: u8 = 0b001000;
pub const ADDIU: u8 = 0b001001;
pub const SLTI: u8 = 0b001010;
pub const SLTIU: u8 = 0b001011;
pub const ANDI: u8 = 0b001100;
pub const ORI: u8 = 0b001101;
pub const XORI: u8 = 0b001110;
pub const LLO: u8 = 0b011000;
pub const LHI: u8 = 0b011001;
pub const SYSCALL: u8 = 0b011010;
pub const LB: u8 = 0b100000;
pub const LH: u8 = 0b100001;
pub const LW: u8 = 0b100011;
pub const LBU: u8 = 0b100100;
pub const LHU: u8 = 0b100101;
pub const SB: u8 = 0b101000;
pub const SH: u8 = 0b101001;
pub const SW: u8 = 0b101011;

#[derive(Debug, EnumString)]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
pub enum Op {
    REG = REG,
    J = J,
    JAL = JAL,
    BEQ = BEQ,
    BNE = BNE,
    BLEZ = BLEZ,
    BGTZ = BGTZ,
    ADDI = ADDI,
    ADDIU = ADDIU,
    SLTI = SLTI,
    SLTIU = SLTIU,
    ANDI = ANDI,
    ORI = ORI,
    XORI = XORI,
    LLO = LLO,
    LHI = LHI,
    SYSCALL = SYSCALL,
    LB = LB,
    LH = LH,
    LW = LW,
    LBU = LBU,
    LHU = LHU,
    SB = SB,
    SH = SH,
    SW = SW,
}

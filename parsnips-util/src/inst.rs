use num_enum::TryFromPrimitive;
use parsnips_util_proc_macro::from_encoding_table;

pub mod regimm;
pub mod special;
pub mod special3;

pub type Inst = u32;

#[from_encoding_table[
    // spec table A.2
    //        000      001     010   011    100   101   110    111
    /* 000 */ SPECIAL, REGIMM, J   , JAL  , BEQ , BNE , POP06, POP07   ,
    /* 001 */ POP10  , ADDIU , SLTI, SLTIU, ANDI, ORI , XORI , AUI     ,
    /* 010 */ COP0   , COP1  , COP2, _    , _   , _   , POP26, POP27   ,
    /* 011 */ POP30  , _     , _   , _    , _   , _   , MSA  , SPECIAL3,
    /* 100 */ LB     , LH    , _   , LW   , LBU , LHU , _    , _       ,
    /* 101 */ SB     , SH    , _   , SW   , _   , _   , _    , CACHE   ,
    /* 110 */ LL     , LWC1  , BC  , PREF , _   , LDC1, POP66, _       ,
    /* 111 */ SC     , SWC1  , BALC, PCREL, _   , SDC1, POP76, _       ,
]]
#[derive(TryFromPrimitive)]
#[repr(u8)]
pub enum Opcode {}

pub trait InstFields {
    fn opcode(&self) -> Option<Opcode>;
}

impl InstFields for Inst {
    fn opcode(&self) -> Option<Opcode> {
        ((self >> 26) as u8).try_into().ok()
    }
}

pub trait ArithIFields {
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
    fn imm(&self) -> u16;
}

impl ArithIFields for Inst {
    fn rs(&self) -> usize {
        ((self >> 21) & ((1 << 5) - 1)) as usize
    }
    fn rt(&self) -> usize {
        ((self >> 16) & ((1 << 5) - 1)) as usize
    }
    fn imm(&self) -> u16 {
        (self & ((1 << 16) - 1)) as u16
    }
}

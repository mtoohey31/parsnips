use arbitrary_int::u5;
use bitbybit::{bitenum, bitfield};
use parsnips_util_proc_macro::from_encoding_table;

use self::special::Special;
use super::reg::Reg;

pub mod regimm;
pub mod special;
pub mod special3;

#[from_encoding_table[
    // spec vol II-A table A.2
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
#[bitenum(u6, exhaustive: false)]
pub enum Opcode {}

// generic encodings, described in spec vol I-A section 5.7.2
// some other instruction-specific encodings are defined in other modules

#[bitfield(u32)]
pub struct Inst {
    #[bits(26..=31, rw)]
    opcode: Option<Opcode>,
}

#[bitfield(u32)]
pub struct RInst {
    #[bits(21..=25, rw)]
    rs: Reg,
    #[bits(16..=20, rw)]
    rt: Reg,
    #[bits(11..=15, rw)]
    rd: Reg,
    #[bits(6..=10, rw)]
    sa: u5,
    #[bits(0..=5, rw)]
    function: Option<Special>,
}

#[bitfield(u32)]
pub struct Imm16Inst {
    #[bits(21..=25, rw)]
    rs: Reg,
    #[bits(16..=20, rw)]
    rt: Reg,
    #[bits(0..=15, rw)]
    immediate: u16,
}

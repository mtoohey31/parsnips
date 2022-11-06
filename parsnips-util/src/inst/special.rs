use super::Inst;
use num_enum::TryFromPrimitive;
use parsnips_util_proc_macro::from_encoding_table;

#[from_encoding_table[
    // spec table A.3
    //        000    001    010    011    100      101     110    111
    /* 000 */ SLL  , _    , SRL  , SRA  , SLLV   , LSA   , SRLV , SRAV  ,
    /* 001 */ _    , JALR , _    , _    , SYSCALL, BREAK , SDBBP, SYNC  ,
    /* 010 */ CLZ  , CLO  , _    , _    , _      , _     , _    , _     ,
    /* 011 */ SOP30, SOP31, SOP32, SOP33, _      , _     , _    , _     ,
    /* 100 */ ADD  , ADDU , SUB  , SUBU , AND    , OR    , XOR  , NOR   ,
    /* 101 */ _    , _    , SLT  , SLTU , _      , _     , _    , _     ,
    /* 110 */ TGE  , TGEU , TLT  , TLTU , TEQ    , SELEQZ, TNE  , SELNEZ,
    /* 111 */ _    , _    , _    , _    , _      , _     , _    , _     ,
]]
#[derive(TryFromPrimitive)]
#[repr(u8)]
pub enum Special {}

pub trait SpecialFields {
    fn rs(&self) -> usize;
    fn rt(&self) -> usize;
    fn rd(&self) -> usize;
    fn sa(&self) -> u32;
    fn function(&self) -> Option<Special>;
}

impl SpecialFields for Inst {
    fn rs(&self) -> usize {
        ((self >> 21) & ((1 << 5) - 1)) as usize
    }
    fn rt(&self) -> usize {
        ((self >> 16) & ((1 << 5) - 1)) as usize
    }
    fn rd(&self) -> usize {
        ((self >> 11) & ((1 << 5) - 1)) as usize
    }
    fn sa(&self) -> u32 {
        ((self >> 6) & ((1 << 5) - 1)) as u32
    }
    fn function(&self) -> Option<Special> {
        ((self & ((1 << 6) - 1)) as u8).try_into().ok()
    }
}

use super::Inst;
use num_enum::TryFromPrimitive;
use parsnips_util_proc_macro::from_encoding_table;

#[from_encoding_table[
    // spec table A.4
    //       000   001   010 011 100 101 110   111
    /* 00 */ BLTZ, BGEZ, _ , _ , _ , _ , DAHI, _     ,
    /* 01 */ _   , _   , _ , _ , _ , _ , _   , _     ,
    /* 10 */ NAL , BAL , _ , _ , _ , _ , _   , SIGRIE,
    /* 11 */ _   , _   , _ , _ , _ , _ , DATI, SYNCI ,
]]
#[derive(TryFromPrimitive)]
#[repr(u8)]
pub enum Regimm {}

pub trait RegimmFields {
    fn rt(&self) -> Option<Regimm>;
}

impl RegimmFields for Inst {
    fn rt(&self) -> Option<Regimm> {
        (((self >> 16) & ((1 << 5) - 1)) as u8).try_into().ok()
    }
}

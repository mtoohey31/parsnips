use bitbybit::{bitenum, bitfield};
use parsnips_util_proc_macro::from_encoding_table;

#[from_encoding_table[
    // spec vol II-A table A.6
    //        000    001  010 011     100  101    110  111
    /* 000 */ EXT  , _   , _, _     , INS, _    , _  , _  ,
    /* 001 */ _    , _   , _, _     , _  , _    , _  , CRC,
    /* 010 */ _    , _   , _, _     , _  , _    , _  , _  ,
    /* 011 */ _    , _   , _, CACHEE, SBE, SHE  , SCE, SWE,
    /* 100 */ BSHFL, _   , _, PREFE , _  , CACHE, SC , _  ,
    /* 101 */ LBUE , LHUE, _, _     , LBE, LHE  , LLE, LWE,
    /* 110 */ _    , _   , _, _     , _  , PREF , LL , _  ,
    /* 111 */ _    , _   , _, RDHWR , _  , GINV , _  , _  ,
]]
#[bitenum(u6, exhaustive: false)]
pub enum Special3 {}

#[bitfield(u32)]
pub struct Special3Inst {
    #[bits(0..=5, rw)]
    function: Option<Special3>,
}

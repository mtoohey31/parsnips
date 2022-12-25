use bitbybit::bitenum;
use parsnips_util_proc_macro::from_encoding_table;

#[from_encoding_table[
    // spec vol II-A table A.4
    //       000   001   010 011 100 101 110   111
    /* 00 */ BLTZ, BGEZ, _ , _ , _ , _ , DAHI, _     ,
    /* 01 */ _   , _   , _ , _ , _ , _ , _   , _     ,
    /* 10 */ NAL , BAL , _ , _ , _ , _ , _   , SIGRIE,
    /* 11 */ _   , _   , _ , _ , _ , _ , DATI, SYNCI ,
]]
#[bitenum(u5, exhaustive: false)]
pub enum Regimm {}

use parsnips_util_proc_macro::encoding_table;

#[rustfmt::skip]
encoding_table![Opcode: // spec table A.2
    //        000      001     010   011    100   101   110    111
    /* 000 */ SPECIAL, REGIMM, J   , JAL  , BEQ , BNE , POP06, POP07   ,
    /* 001 */ POP10  , ADDIU , SLTI, SLTIU, ANDI, ORI , XORI , AUI     ,
    /* 010 */ COP0   , COP1  , COP2, _    , _   , _   , POP26, POP27   ,
    /* 011 */ POP30  , _     , _   , _    , _   , _   , MSA  , SPECIAL3,
    /* 100 */ LB     , LH    , _   , LW   , LBU , LHU , _    , _       ,
    /* 101 */ SB     , SH    , _   , SW   , _   , _   , _    , CACHE   ,
    /* 110 */ LL     , LWC1  , BC  , PREF , _   , LDC1, POP66, _       ,
    /* 111 */ SC     , SWC1  , BALC, PCREL, _   , SDC1, POP76, _       ,
];

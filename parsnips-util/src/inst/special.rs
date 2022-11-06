use parsnips_util_proc_macro::encoding_table;

#[rustfmt::skip]
encoding_table![Special: // spec table A.3
    //        000    001    010    011    100      101     110    111
    /* 000 */ SLL  , _    , SRL  , SRA  , SLLV   , LSA   , SRLV , SRAV  ,
    /* 001 */ _    , JALR , _    , _    , SYSCALL, BREAK , SDBBP, SYNC  ,
    /* 010 */ CLZ  , CLO  , _    , _    , _      , _     , _    , _     ,
    /* 011 */ SOP30, SOP31, SOP32, SOP33, _      , _     , _    , _     ,
    /* 100 */ ADD  , ADDU , SUB  , SUBU , AND    , OR    , XOR  , NOR   ,
    /* 101 */ _    , _    , SLT  , SLTU , _      , _     , _    , _     ,
    /* 110 */ TGE  , TGEU , TLT  , TLTU , TEQ    , SELEQZ, TNE  , SELNEZ,
    /* 111 */ _    , _    , _    , _    , _      , _     , _    , _     ,
];

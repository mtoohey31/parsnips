use parsnips_util_proc_macro::encoding_table;

#[rustfmt::skip]
encoding_table![Special3: // spec table A.6
    //        000    001  010 011     100  101    110  111
    /* 000 */ EXT  , _   , _, _     , INS, _    , _  , _  ,
    /* 001 */ _    , _   , _, _     , _  , _    , _  , _  ,
    /* 010 */ _    , _   , _, _     , _  , _    , _  , _  ,
    /* 011 */ _    , _   , _, CACHEE, SBE, SHE  , SCE, SWE,
    /* 100 */ BSHFL, _   , _, PREFE , _  , CACHE, SC , _  ,
    /* 101 */ LBUE , LHUE, _, _     , LBE, LHE  , LLE, LWE,
    /* 110 */ _    , _   , _, _     , _  , PREF , LL , _  ,
    /* 111 */ _    , _   , _, RDHWR , _  , _    , _  , _  ,
];

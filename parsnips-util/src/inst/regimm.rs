use parsnips_util_proc_macro::encoding_table;

#[rustfmt::skip]
encoding_table![Regimm: // spec table A.4
    //       000   001   010 011 100 101 110   111
    /* 00 */ BLTZ, BGEZ, _ , _ , _ , _ , DAHI, _     ,
    /* 01 */ _   , _   , _ , _ , _ , _ , _   , _     ,
    /* 10 */ NAL , BAL , _ , _ , _ , _ , _   , SIGRIE,
    /* 11 */ _   , _   , _ , _ , _ , _ , DATI, SYNCI ,
];

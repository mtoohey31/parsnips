use parsnips_parser::{MIPSParser, Rule};
use pest::{consumes_to, parses_to};
use std::fmt;

struct DisplayPair<'i, R: pest::RuleType>(pest::iterators::Pair<'i, R>);

impl<'i, R: pest::RuleType> fmt::Debug for DisplayPair<'i, R> {
    // TODO: remove trailing comma after final tuple field
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let span = self.0.clone().as_span();
        let rule = format!("{:?}", self.0.as_rule());
        let inner: Vec<_> = self.0.clone().into_inner().map(DisplayPair).collect();
        f.debug_tuple(&rule)
            .field(&span.start_pos().pos())
            .field(&span.end_pos().pos())
            .field(&inner)
            .finish()
    }
}

#[test]
fn test_fibonacci() {
    // dbg!(
    //     MIPSParser::parse(Rule::file, include_str!("./Fibonacci.asm"))
    //         .unwrap()
    //         .map(|p| DisplayPair(p))
    //         .collect::<Vec<_>>()
    // );

    let input = include_str!("./Fibonacci.asm").replace("\r\n", "\n");

    parses_to! {
        parser: MIPSParser,
        input: &input,
        rule: Rule::file,
        tokens: [
            file(
                0,
                2391,
                [
                    dataSection(
                        138,
                        231,
                        [
                            label(
                                144,
                                149,
                                []
                            ),
                            size(
                                150,
                                155,
                                []
                            ),
                            value(
                                158,
                                164,
                                [
                                    array(
                                        158,
                                        164,
                                        [
                                            int(
                                                158,
                                                159,
                                                []
                                            ),
                                            int(
                                                162,
                                                164,
                                                []
                                            ),
                                        ]
                                    ),
                                ]
                            ),
                            label(
                                216,
                                221,
                                []
                            ),
                            size(
                                222,
                                227,
                                []
                            ),
                            value(
                                229,
                                231,
                                [
                                    int(
                                        229,
                                        231,
                                        []
                                    ),
                                ]
                            ),
                        ]
                    ),
                    textSection(
                        269,
                        1339,
                        [
                            instruction(
                                281,
                                295,
                                [
                                    instructionIdent(
                                        281,
                                        283,
                                        []
                                    ),
                                    reg(
                                        286,
                                        289,
                                        []
                                    ),
                                    dataIdent(
                                        291,
                                        295,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                333,
                                347,
                                [
                                    instructionIdent(
                                        333,
                                        335,
                                        []
                                    ),
                                    reg(
                                        338,
                                        341,
                                        []
                                    ),
                                    dataIdent(
                                        343,
                                        347,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                393,
                                409,
                                [
                                    instructionIdent(
                                        393,
                                        395,
                                        []
                                    ),
                                    reg(
                                        398,
                                        401,
                                        []
                                    ),
                                    offsetReg(
                                        403,
                                        409,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                439,
                                450,
                                [
                                    instructionIdent(
                                        439,
                                        441,
                                        []
                                    ),
                                    reg(
                                        444,
                                        447,
                                        []
                                    ),
                                    dataIdent(
                                        449,
                                        450,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                503,
                                522,
                                [
                                    instructionIdent(
                                        503,
                                        508,
                                        []
                                    ),
                                    reg(
                                        509,
                                        512,
                                        []
                                    ),
                                    reg(
                                        514,
                                        517,
                                        []
                                    ),
                                    reg(
                                        519,
                                        522,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                529,
                                545,
                                [
                                    instructionIdent(
                                        529,
                                        531,
                                        []
                                    ),
                                    reg(
                                        534,
                                        537,
                                        []
                                    ),
                                    offsetReg(
                                        539,
                                        545,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                568,
                                584,
                                [
                                    instructionIdent(
                                        568,
                                        570,
                                        []
                                    ),
                                    reg(
                                        573,
                                        576,
                                        []
                                    ),
                                    offsetReg(
                                        578,
                                        584,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                614,
                                631,
                                [
                                    instructionIdent(
                                        614,
                                        618,
                                        []
                                    ),
                                    reg(
                                        619,
                                        622,
                                        []
                                    ),
                                    reg(
                                        624,
                                        627,
                                        []
                                    ),
                                    int(
                                        629,
                                        631,
                                        []
                                    ),
                                ]
                            ),
                            label(
                                684,
                                689,
                                []
                            ),
                            instruction(
                                690,
                                706,
                                [
                                    instructionIdent(
                                        690,
                                        692,
                                        []
                                    ),
                                    reg(
                                        695,
                                        698,
                                        []
                                    ),
                                    offsetReg(
                                        700,
                                        706,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                747,
                                763,
                                [
                                    instructionIdent(
                                        747,
                                        749,
                                        []
                                    ),
                                    reg(
                                        752,
                                        755,
                                        []
                                    ),
                                    offsetReg(
                                        757,
                                        763,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                805,
                                823,
                                [
                                    instructionIdent(
                                        805,
                                        808,
                                        []
                                    ),
                                    reg(
                                        810,
                                        813,
                                        []
                                    ),
                                    reg(
                                        815,
                                        818,
                                        []
                                    ),
                                    reg(
                                        820,
                                        823,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                855,
                                871,
                                [
                                    instructionIdent(
                                        855,
                                        857,
                                        []
                                    ),
                                    reg(
                                        860,
                                        863,
                                        []
                                    ),
                                    offsetReg(
                                        865,
                                        871,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                923,
                                939,
                                [
                                    instructionIdent(
                                        923,
                                        927,
                                        []
                                    ),
                                    reg(
                                        928,
                                        931,
                                        []
                                    ),
                                    reg(
                                        933,
                                        936,
                                        []
                                    ),
                                    dataIdent(
                                        938,
                                        939,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                993,
                                1010,
                                [
                                    instructionIdent(
                                        993,
                                        997,
                                        []
                                    ),
                                    reg(
                                        998,
                                        1001,
                                        []
                                    ),
                                    reg(
                                        1003,
                                        1006,
                                        []
                                    ),
                                    int(
                                        1008,
                                        1010,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1046,
                                1060,
                                [
                                    instructionIdent(
                                        1046,
                                        1050,
                                        []
                                    ),
                                    reg(
                                        1051,
                                        1054,
                                        []
                                    ),
                                    dataIdent(
                                        1056,
                                        1060,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1104,
                                1118,
                                [
                                    instructionIdent(
                                        1104,
                                        1106,
                                        []
                                    ),
                                    reg(
                                        1109,
                                        1112,
                                        []
                                    ),
                                    dataIdent(
                                        1114,
                                        1118,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1167,
                                1187,
                                [
                                    instructionIdent(
                                        1167,
                                        1170,
                                        []
                                    ),
                                    reg(
                                        1172,
                                        1175,
                                        []
                                    ),
                                    reg(
                                        1177,
                                        1182,
                                        []
                                    ),
                                    reg(
                                        1184,
                                        1187,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1230,
                                1281,
                                [
                                    instructionIdent(
                                        1230,
                                        1233,
                                        []
                                    ),
                                    dataIdent(
                                        1235,
                                        1240,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1281,
                                1293,
                                [
                                    instructionIdent(
                                        1281,
                                        1283,
                                        []
                                    ),
                                    reg(
                                        1286,
                                        1289,
                                        []
                                    ),
                                    dataIdent(
                                        1291,
                                        1293,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1332,
                                1339,
                                []
                            ),
                        ]
                    ),
                    dataSection(
                        1440,
                        1553,
                        [
                            label(
                                1446,
                                1452,
                                []
                            ),
                            size(
                                1452,
                                1459,
                                []
                            ),
                            value(
                                1461,
                                1464,
                                [
                                    string(
                                        1461,
                                        1464,
                                        [
                                            inner(
                                                1462,
                                                1463,
                                                []
                                            ),
                                        ]
                                    ),
                                ]
                            ),
                            label(
                                1508,
                                1513,
                                []
                            ),
                            size(
                                1514,
                                1521,
                                []
                            ),
                            value(
                                1523,
                                1553,
                                [
                                    string(
                                        1523,
                                        1553,
                                        [
                                            inner(
                                                1524,
                                                1552,
                                                []
                                            ),
                                        ]
                                    ),
                                ]
                            ),
                        ]
                    ),
                    textSection(
                        1560,
                        2391,
                        [
                            label(
                                1566,
                                1572,
                                []
                            ),
                            instruction(
                                1572,
                                1592,
                                [
                                    instructionIdent(
                                        1572,
                                        1575,
                                        []
                                    ),
                                    reg(
                                        1577,
                                        1580,
                                        []
                                    ),
                                    reg(
                                        1582,
                                        1587,
                                        []
                                    ),
                                    reg(
                                        1589,
                                        1592,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1628,
                                1648,
                                [
                                    instructionIdent(
                                        1628,
                                        1631,
                                        []
                                    ),
                                    reg(
                                        1633,
                                        1636,
                                        []
                                    ),
                                    reg(
                                        1638,
                                        1643,
                                        []
                                    ),
                                    reg(
                                        1645,
                                        1648,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1696,
                                1710,
                                [
                                    instructionIdent(
                                        1696,
                                        1698,
                                        []
                                    ),
                                    reg(
                                        1701,
                                        1704,
                                        []
                                    ),
                                    dataIdent(
                                        1706,
                                        1710,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1756,
                                1767,
                                [
                                    instructionIdent(
                                        1756,
                                        1758,
                                        []
                                    ),
                                    reg(
                                        1761,
                                        1764,
                                        []
                                    ),
                                    dataIdent(
                                        1766,
                                        1767,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1815,
                                1822,
                                []
                            ),
                            label(
                                1853,
                                1857,
                                []
                            ),
                            instruction(
                                1859,
                                1875,
                                [
                                    instructionIdent(
                                        1859,
                                        1861,
                                        []
                                    ),
                                    reg(
                                        1864,
                                        1867,
                                        []
                                    ),
                                    offsetReg(
                                        1869,
                                        1875,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1923,
                                1934,
                                [
                                    instructionIdent(
                                        1923,
                                        1925,
                                        []
                                    ),
                                    reg(
                                        1928,
                                        1931,
                                        []
                                    ),
                                    dataIdent(
                                        1933,
                                        1934,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                1983,
                                1990,
                                []
                            ),
                            instruction(
                                2036,
                                2051,
                                [
                                    instructionIdent(
                                        2036,
                                        2038,
                                        []
                                    ),
                                    reg(
                                        2041,
                                        2044,
                                        []
                                    ),
                                    dataIdent(
                                        2046,
                                        2051,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                2101,
                                2112,
                                [
                                    instructionIdent(
                                        2101,
                                        2103,
                                        []
                                    ),
                                    reg(
                                        2106,
                                        2109,
                                        []
                                    ),
                                    dataIdent(
                                        2111,
                                        2112,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                2160,
                                2167,
                                []
                            ),
                            instruction(
                                2204,
                                2220,
                                [
                                    instructionIdent(
                                        2204,
                                        2208,
                                        []
                                    ),
                                    reg(
                                        2209,
                                        2212,
                                        []
                                    ),
                                    reg(
                                        2214,
                                        2217,
                                        []
                                    ),
                                    dataIdent(
                                        2219,
                                        2220,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                2252,
                                2269,
                                [
                                    instructionIdent(
                                        2252,
                                        2256,
                                        []
                                    ),
                                    reg(
                                        2257,
                                        2260,
                                        []
                                    ),
                                    reg(
                                        2262,
                                        2265,
                                        []
                                    ),
                                    int(
                                        2267,
                                        2269,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                2305,
                                2318,
                                [
                                    instructionIdent(
                                        2305,
                                        2309,
                                        []
                                    ),
                                    reg(
                                        2310,
                                        2313,
                                        []
                                    ),
                                    dataIdent(
                                        2315,
                                        2318,
                                        []
                                    ),
                                ]
                            ),
                            instruction(
                                2358,
                                2391,
                                [
                                    instructionIdent(
                                        2358,
                                        2360,
                                        []
                                    ),
                                    reg(
                                        2363,
                                        2366,
                                        []
                                    ),
                                ]
                            ),
                        ]
                    ),
                    EOI(
                        2391,
                        2391,
                        []
                    ),
                ]
            )
        ]
    };
}

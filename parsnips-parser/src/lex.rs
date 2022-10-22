extern crate alloc;
use alloc::vec::Vec;

use crate::{Literal, NumLiteral};

#[derive(Debug, PartialEq, Eq)]
pub struct Token<'a> {
    pub pos: usize,
    pub kind: TokenKind<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind<'a> {
    Dot,
    Comma,
    Colon,
    OpenParen,
    CloseParen,
    Dollar,
    Whitespace,
    Newline,
    Ident(&'a str),
    Comment(&'a str),
    Literal(Literal<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct LexError {
    pub pos: usize,
    pub kind: LexErrorKind,
}

#[derive(Debug, PartialEq, Eq)]
pub enum LexErrorKind {
    UnexpectedToken(char),
    InvalidCharEscape(char),
    UnterminatedChar,
    NonSingleChar,
    UnterminatedStr,
    UnterminatedNum,
}

macro_rules! failing_pos {
    ($f:expr, $ci:expr, $x:expr) => {{
        let mut f = $f;
        loop {
            match $ci.peek() {
                Some((nf, c)) => {
                    f = *nf;
                    if !$x(*c) {
                        break;
                    }

                    $ci.next().unwrap();
                }
                None => {
                    f += 1;
                    break;
                }
            }
        }
        f
    }};
}

pub fn lex<'a>(input: &'a str) -> Result<Vec<Token<'a>>, LexError> {
    let mut ci = input.char_indices().peekable();
    let mut tokens = Vec::new();
    'OUTER: while let Some((pos, mut c)) = ci.next() {
        match c {
            '0'..='9' | '-' => {
                let negative = c == '-';
                let mut body_pos = pos;
                if negative {
                    (body_pos, c) = ci.next().ok_or(LexError {
                        pos,
                        kind: LexErrorKind::UnterminatedNum,
                    })?;
                    if !matches!(c, '0'..='9') {
                        return Err(LexError {
                            pos: body_pos,
                            kind: LexErrorKind::UnterminatedNum,
                        });
                    }
                }
                tokens.push(Token {
                    pos,
                    kind: TokenKind::Literal(if c == '0' {
                        match ci.peek() {
                            Some((_, 'b')) => {
                                ci.next().unwrap();
                                Literal::Num(NumLiteral {
                                    negative,
                                    radix: 2,
                                    body: &input[body_pos + 2
                                        ..failing_pos!(body_pos + 2, ci, is_binary_digit)],
                                })
                            }
                            Some((_, 'o')) => {
                                ci.next().unwrap();
                                Literal::Num(NumLiteral {
                                    negative,
                                    radix: 8,
                                    body: &input[body_pos + 2
                                        ..failing_pos!(body_pos + 2, ci, is_octal_digit)],
                                })
                            }
                            Some((_, 'x')) => {
                                ci.next().unwrap();
                                Literal::Num(NumLiteral {
                                    negative,
                                    radix: 16,
                                    body: &input[body_pos + 2
                                        ..failing_pos!(body_pos + 2, ci, is_hex_digit)],
                                })
                            }
                            _ => Literal::Num(NumLiteral {
                                negative,
                                radix: 10,
                                body: &input
                                    [body_pos..failing_pos!(body_pos, ci, is_decimal_digit)],
                            }),
                        }
                    } else {
                        Literal::Num(NumLiteral {
                            negative,
                            radix: 10,
                            body: &input[body_pos..failing_pos!(body_pos, ci, is_decimal_digit)],
                        })
                    }),
                });
            }
            '\'' => {
                let res = match ci.next() {
                    Some((pos, '\\')) => match ci.next() {
                        Some((pos, 't')) => Token {
                            pos,
                            kind: TokenKind::Literal(Literal::Char('\t')),
                        },
                        Some((pos, 'n')) => Token {
                            pos,
                            kind: TokenKind::Literal(Literal::Char('\n')),
                        },
                        Some((pos, '\\')) => Token {
                            pos,
                            kind: TokenKind::Literal(Literal::Char('\\')),
                        },
                        Some((pos, c)) => {
                            return Err(LexError {
                                pos,
                                kind: LexErrorKind::InvalidCharEscape(c),
                            })
                        }
                        None => {
                            return Err(LexError {
                                pos: pos + 1,
                                kind: LexErrorKind::UnterminatedChar,
                            })
                        }
                    },
                    Some((pos, c)) => Token {
                        pos,
                        kind: TokenKind::Literal(Literal::Char(c)),
                    },
                    None => {
                        return Err(LexError {
                            pos: pos + 1,
                            kind: LexErrorKind::UnterminatedChar,
                        })
                    }
                };
                let (pos, c) = ci.next().ok_or(LexError {
                    pos,
                    kind: LexErrorKind::UnterminatedChar,
                })?;
                if c != '\'' {
                    return Err(LexError {
                        pos,
                        kind: LexErrorKind::NonSingleChar,
                    });
                };
                tokens.push(res);
            }
            '"' => {
                while let Some((curr_pos, c)) = ci.next() {
                    match c {
                        '"' => {
                            tokens.push(Token {
                                pos,
                                kind: TokenKind::Literal(Literal::Str(&input[pos + 1..curr_pos])),
                            });
                            continue 'OUTER;
                        }
                        '\\' => {
                            handle_escape(ci.next().ok_or(LexError {
                                pos,
                                kind: LexErrorKind::UnterminatedStr,
                            })?)?;
                        }
                        _ => {}
                    }
                }
                return Err(LexError {
                    pos,
                    kind: LexErrorKind::UnterminatedStr,
                });
            }
            '#' => tokens.push(Token {
                pos,
                kind: TokenKind::Comment(
                    &input[pos + 1..failing_pos!(pos, ci, |c| !is_newline(c))],
                ),
            }),
            '.' => tokens.push(Token {
                pos,
                kind: TokenKind::Dot,
            }),
            ',' => tokens.push(Token {
                pos,
                kind: TokenKind::Comma,
            }),
            ':' => tokens.push(Token {
                pos,
                kind: TokenKind::Colon,
            }),
            '(' => tokens.push(Token {
                pos,
                kind: TokenKind::OpenParen,
            }),
            ')' => tokens.push(Token {
                pos,
                kind: TokenKind::CloseParen,
            }),
            '$' => tokens.push(Token {
                pos,
                kind: TokenKind::Dollar,
            }),
            '\n' | '\u{0085}' | '\u{2029}' => tokens.push(Token {
                pos,
                kind: TokenKind::Newline,
            }),

            c if is_whitespace(c) => tokens.push(Token {
                pos,
                kind: TokenKind::Whitespace,
            }),

            c if is_ident_start(c) => tokens.push(Token {
                pos,
                kind: TokenKind::Ident(&input[pos..failing_pos!(pos, ci, is_ident)]),
            }),

            _ => {
                return Err(LexError {
                    pos,
                    kind: LexErrorKind::UnexpectedToken(c),
                })
            }
        };
    }
    Ok(tokens)
}

#[inline(always)]
fn is_newline(c: char) -> bool {
    c == '\n'
}

#[inline(always)]
fn is_whitespace(c: char) -> bool {
    // taken from https://github.com/rust-lang/rust/blob/master/compiler/rustc_lexer/src/lib.rs
    is_newline(c)
        || matches!(
            c,
            '\t' | '\u{000B}'
                | '\u{000C}'
                | '\r'
                | ' '
                | '\u{0085}'
                | '\u{200E}'
                | '\u{200F}'
                | '\u{2028}'
                | '\u{2029}'
        )
}

#[inline(always)]
fn is_decimal_digit(c: char) -> bool {
    matches!(c, '0'..='9')
}

#[inline(always)]
fn is_binary_digit(c: char) -> bool {
    matches!(c, '0' | '1')
}

#[inline(always)]
fn is_octal_digit(c: char) -> bool {
    matches!(c, '0'..='7')
}

#[inline(always)]
fn is_hex_digit(c: char) -> bool {
    matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F')
}

#[inline(always)]
fn is_ident_start(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_')
}

#[inline(always)]
fn is_ident(c: char) -> bool {
    is_ident_start(c) || is_decimal_digit(c) || c == '.'
}

#[inline(always)]
fn handle_escape((pos, c): (usize, char)) -> Result<char, LexError> {
    match c {
        't' => Ok('\t'),
        'n' => Ok('\n'),
        '\\' => Ok('\\'),
        c => Err(LexError {
            pos,
            kind: LexErrorKind::InvalidCharEscape(c),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use pretty_assertions::assert_eq;

    #[test]
    fn basic() {
        assert_eq!(
            lex(include_str!("../../test/basic.asm"))
                .unwrap()
                .into_iter()
                .filter(|t| t.kind != TokenKind::Whitespace)
                .collect::<Vec<_>>(),
            vec![
                Token {
                    pos: 6,
                    kind: TokenKind::Dot
                },
                Token {
                    pos: 7,
                    kind: TokenKind::Ident("text")
                },
                Token {
                    pos: 11,
                    kind: TokenKind::Newline
                },
                Token {
                    pos: 18,
                    kind: TokenKind::Ident("addi")
                },
                Token {
                    pos: 23,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 24,
                    kind: TokenKind::Ident("t0")
                },
                Token {
                    pos: 26,
                    kind: TokenKind::Comma
                },
                Token {
                    pos: 28,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 29,
                    kind: TokenKind::Ident("zero")
                },
                Token {
                    pos: 33,
                    kind: TokenKind::Comma
                },
                Token {
                    pos: 35,
                    kind: TokenKind::Literal(Literal::Num(NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "13"
                    }))
                },
                Token {
                    pos: 37,
                    kind: TokenKind::Newline
                },
                Token {
                    pos: 44,
                    kind: TokenKind::Ident("addi")
                },
                Token {
                    pos: 49,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 50,
                    kind: TokenKind::Ident("t1")
                },
                Token {
                    pos: 52,
                    kind: TokenKind::Comma
                },
                Token {
                    pos: 54,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 55,
                    kind: TokenKind::Ident("zero")
                },
                Token {
                    pos: 59,
                    kind: TokenKind::Comma
                },
                Token {
                    pos: 61,
                    kind: TokenKind::Literal(Literal::Num(NumLiteral {
                        negative: false,
                        radix: 10,
                        body: "26"
                    }))
                },
                Token {
                    pos: 63,
                    kind: TokenKind::Newline
                },
                Token {
                    pos: 70,
                    kind: TokenKind::Ident("add")
                },
                Token {
                    pos: 74,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 75,
                    kind: TokenKind::Ident("t2")
                },
                Token {
                    pos: 77,
                    kind: TokenKind::Comma
                },
                Token {
                    pos: 79,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 80,
                    kind: TokenKind::Ident("t0")
                },
                Token {
                    pos: 82,
                    kind: TokenKind::Comma
                },
                Token {
                    pos: 84,
                    kind: TokenKind::Dollar
                },
                Token {
                    pos: 85,
                    kind: TokenKind::Ident("t1")
                },
                Token {
                    pos: 87,
                    kind: TokenKind::Newline
                },
            ]
        )
    }

    #[test]
    fn comment() {
        assert_eq!(
            lex("# a comment").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Comment(" a comment")
            }]
        )
    }

    #[test]
    fn int() {
        assert_eq!(
            lex("-5894").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: true,
                    radix: 10,
                    body: "5894"
                }))
            }]
        )
    }

    #[test]
    fn uint() {
        assert_eq!(
            lex("5894").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: "5894"
                }))
            }]
        )
    }

    #[test]
    fn negative_overflow() {
        assert_eq!(
            lex("-584654654654654654694").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: true,
                    radix: 10,
                    body: "584654654654654654694"
                }))
            }]
        )
    }

    #[test]
    fn positive_overflow() {
        assert_eq!(
            lex("584654654654654654694").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: false,
                    radix: 10,
                    body: "584654654654654654694"
                }))
            }]
        )
    }

    #[test]
    fn binary() {
        assert_eq!(
            lex("-0b0100").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: true,
                    radix: 2,
                    body: "0100"
                }))
            }]
        )
    }

    #[test]
    fn ocatal() {
        assert_eq!(
            lex("-0o0700").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: true,
                    radix: 8,
                    body: "0700"
                }))
            }]
        )
    }

    #[test]
    fn hex() {
        assert_eq!(
            lex("-0x0AbE").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Num(NumLiteral {
                    negative: true,
                    radix: 16,
                    body: "0AbE"
                }))
            }]
        )
    }

    #[test]
    fn string_simple() {
        assert_eq!(
            lex("\"a string\"").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Literal(Literal::Str("a string"))
            }]
        )
    }

    #[test]
    fn dot_ident() {
        assert_eq!(
            lex("add.d").unwrap(),
            vec![Token {
                pos: 0,
                kind: TokenKind::Ident("add.d")
            }]
        )
    }
}

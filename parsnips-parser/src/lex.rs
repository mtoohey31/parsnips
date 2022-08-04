extern crate alloc;
use alloc::vec::Vec;

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum Token<'a> {
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
    Literal(LiteralToken<'a>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum NumKind {
    Binary,
    Octal,
    Decimal,
    Hex,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum LiteralToken<'a> {
    Num {
        negative: bool,
        kind: NumKind,
        body: &'a str,
    },
    Char(char),
    Str(&'a str),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum LexErrorKind {
    UnexpectedToken(char),
    InvalidCharEscape(char),
    UnterminatedChar,
    NonSingleChar,
    UnterminatedStr,
    UnterminatedNum,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct LexError {
    pos: (usize, usize),
    kind: LexErrorKind,
}

impl LexError {
    fn at(point: usize, kind: LexErrorKind) -> Self {
        Self {
            pos: (point, point + 1),
            kind,
        }
    }

    fn from(start: usize, end: usize, kind: LexErrorKind) -> Self {
        Self {
            pos: (start, end),
            kind,
        }
    }
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
    'OUTER: while let Some((mut pos, mut c)) = ci.next() {
        match c {
            '0'..='9' | '-' => {
                let negative = c == '-';
                if negative {
                    (pos, c) = ci
                        .next()
                        .ok_or(LexError::at(pos, LexErrorKind::UnterminatedNum))?;
                    if !matches!(c, '0'..='9') {
                        return Err(LexError::at(pos, LexErrorKind::UnterminatedNum));
                    }
                }
                tokens.push(Token::Literal(if c == '0' {
                    match ci.peek() {
                        Some((_, 'b')) => {
                            ci.next().unwrap();
                            LiteralToken::Num {
                                negative,
                                kind: NumKind::Binary,
                                body: &input[pos + 2..failing_pos!(pos + 2, ci, is_binary_digit)],
                            }
                        }
                        Some((_, 'o')) => {
                            ci.next().unwrap();
                            LiteralToken::Num {
                                negative,
                                kind: NumKind::Octal,
                                body: &input[pos + 2..failing_pos!(pos + 2, ci, is_octal_digit)],
                            }
                        }
                        Some((_, 'x')) => {
                            ci.next().unwrap();
                            LiteralToken::Num {
                                negative,
                                kind: NumKind::Hex,
                                body: &input[pos + 2..failing_pos!(pos + 2, ci, is_hex_digit)],
                            }
                        }
                        _ => LiteralToken::Num {
                            negative,
                            kind: NumKind::Decimal,
                            body: &input[pos..failing_pos!(pos, ci, is_decimal_digit)],
                        },
                    }
                } else {
                    LiteralToken::Num {
                        negative,
                        kind: NumKind::Decimal,
                        body: &input[pos..failing_pos!(pos, ci, is_decimal_digit)],
                    }
                }));
            }
            '\'' => {
                let (mut pos, res) = match ci.next() {
                    Some((pos, '\\')) => match ci.next() {
                        Some((pos, 't')) => (pos, Ok(Token::Literal(LiteralToken::Char('\t')))),
                        Some((pos, 'n')) => (pos, Ok(Token::Literal(LiteralToken::Char('\n')))),
                        Some((pos, '\\')) => (pos, Ok(Token::Literal(LiteralToken::Char('\\')))),
                        Some((pos, c)) => (
                            pos,
                            Err(LexError::at(pos, LexErrorKind::InvalidCharEscape(c))),
                        ),
                        None => (
                            pos,
                            Err(LexError::at(pos + 1, LexErrorKind::UnterminatedChar)),
                        ),
                    },
                    Some((pos, c)) => (pos, Ok(Token::Literal(LiteralToken::Char(c)))),
                    None => (
                        pos,
                        Err(LexError::at(pos + 1, LexErrorKind::UnterminatedChar)),
                    ),
                };
                (pos, c) = ci
                    .next()
                    .ok_or(LexError::at(pos, LexErrorKind::UnterminatedChar))?;
                if c != '\'' {
                    return Err(LexError::at(pos, LexErrorKind::NonSingleChar));
                };
                tokens.push(res?);
            }
            '"' => {
                let p = pos;
                while let Some((p, c)) = ci.next() {
                    match c {
                        '"' => {
                            tokens.push(Token::Literal(LiteralToken::Str(&input[pos + 1..p])));
                            continue 'OUTER;
                        }
                        '\\' => {
                            handle_escape(
                                ci.next()
                                    .ok_or(LexError::at(p, LexErrorKind::UnterminatedStr))?,
                            )?;
                        }
                        _ => {}
                    }
                }
                return Err(LexError::at(p, LexErrorKind::UnterminatedStr));
            }
            '#' => tokens.push(Token::Comment(
                &input[pos + 1..failing_pos!(pos, ci, |c| !is_newline(c))],
            )),
            '.' => tokens.push(Token::Dot),
            ',' => tokens.push(Token::Comma),
            ':' => tokens.push(Token::Colon),
            '(' => tokens.push(Token::OpenParen),
            ')' => tokens.push(Token::CloseParen),
            '$' => tokens.push(Token::Dollar),
            '\n' | '\u{0085}' | '\u{2029}' => tokens.push(Token::Newline),

            c if is_whitespace(c) => tokens.push(Token::Whitespace),

            c if is_ident_start(c) => {
                tokens.push(Token::Ident(&input[pos..failing_pos!(pos, ci, is_ident)]))
            }

            _ => return Err(LexError::at(pos, LexErrorKind::UnexpectedToken(c))),
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
        c => Err(LexError::at(pos, LexErrorKind::InvalidCharEscape(c))),
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[test]
    fn basic() {
        assert_eq!(
            lex(include_str!("../tests/basic.asm"))
                .unwrap()
                .into_iter()
                .filter(|t| *t != Token::Whitespace)
                .collect::<Vec<_>>(),
            vec![
                Token::Dot,
                Token::Ident("text"),
                Token::Newline,
                Token::Ident("addi"),
                Token::Dollar,
                Token::Ident("t0"),
                Token::Comma,
                Token::Dollar,
                Token::Ident("zero"),
                Token::Comma,
                Token::Literal(LiteralToken::Num {
                    negative: false,
                    kind: NumKind::Decimal,
                    body: "13"
                }),
                Token::Newline,
                Token::Ident("addi"),
                Token::Dollar,
                Token::Ident("t1"),
                Token::Comma,
                Token::Dollar,
                Token::Ident("zero"),
                Token::Comma,
                Token::Literal(LiteralToken::Num {
                    negative: false,
                    kind: NumKind::Decimal,
                    body: "26"
                }),
                Token::Newline,
                Token::Ident("add"),
                Token::Dollar,
                Token::Ident("t2"),
                Token::Comma,
                Token::Dollar,
                Token::Ident("t0"),
                Token::Comma,
                Token::Dollar,
                Token::Ident("t1"),
                Token::Newline,
            ]
        )
    }

    #[test]
    fn comment() {
        assert_eq!(
            lex("# a comment").unwrap(),
            vec![Token::Comment(" a comment")]
        )
    }

    #[test]
    fn int() {
        assert_eq!(
            lex("-5894").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: true,
                kind: NumKind::Decimal,
                body: "5894"
            })]
        )
    }

    #[test]
    fn uint() {
        assert_eq!(
            lex("5894").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: false,
                kind: NumKind::Decimal,
                body: "5894"
            })]
        )
    }

    #[test]
    fn negative_overflow() {
        assert_eq!(
            lex("-584654654654654654694").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: true,
                kind: NumKind::Decimal,
                body: "584654654654654654694"
            })]
        )
    }

    #[test]
    fn positive_overflow() {
        assert_eq!(
            lex("584654654654654654694").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: false,
                kind: NumKind::Decimal,
                body: "584654654654654654694"
            })]
        )
    }

    #[test]
    fn binary() {
        assert_eq!(
            lex("-0b0100").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: true,
                kind: NumKind::Binary,
                body: "0100"
            })]
        )
    }

    #[test]
    fn ocatal() {
        assert_eq!(
            lex("-0o0700").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: true,
                kind: NumKind::Octal,
                body: "0700"
            })]
        )
    }

    #[test]
    fn hex() {
        assert_eq!(
            lex("-0x0AbE").unwrap(),
            vec![Token::Literal(LiteralToken::Num {
                negative: true,
                kind: NumKind::Hex,
                body: "0AbE"
            })]
        )
    }

    #[test]
    fn string_simple() {
        assert_eq!(
            lex("\"a string\"").unwrap(),
            vec![Token::Literal(LiteralToken::Str("a string"))]
        )
    }

    #[test]
    fn dot_ident() {
        assert_eq!(lex("add.d").unwrap(), vec![Token::Ident("add.d")])
    }
}

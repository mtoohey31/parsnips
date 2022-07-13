use core::{
    iter,
    num::{IntErrorKind, TryFromIntError},
};

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
pub enum LiteralToken<'a> {
    Int(i32),
    Uint(u32),
    Char(char),
    Str(&'a str),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum LexError {
    ParseIntError(IntErrorKind),
    UnexpectedToken(char),
    InvalidCharEscape(char),
    UnterminatedChar,
    NonSingleChar,
}

struct Cursor<'a> {
    input: &'a str,
    current: usize,
}

// TODO: don't use `chars().nth()`, it's really inefficient.
impl<'a> Cursor<'a> {
    fn next(&mut self) -> Option<char> {
        let c = self.input.chars().nth(self.current);
        self.current += 1;
        c
    }

    fn prev(&self) -> Option<char> {
        self.input.chars().nth(self.current - 1)
    }

    fn back(&mut self) {
        self.current -= 1;
    }
}

macro_rules! take_while {
    ($c:expr, $x:expr) => {{
        let start = $c.current;
        while let Some(c) = $c.input.chars().nth($c.current) {
            if !$x(c) {
                break;
            }

            $c.current += 1;
        }
        &$c.input[start..$c.current]
    }};
}

pub fn lex<'a>(input: &'a str) -> impl Iterator<Item = Result<Token<'a>, LexError>> {
    let mut cur = Cursor { input, current: 0 };
    iter::from_fn(move || {
        cur.next().map(|c| match c {
            // TODO: consume the rest of the string, and handle binary, octal, and hex literals
            '0'..='9' | '-' => {
                let negative = cur.prev().unwrap() == '-';
                if negative {
                    cur.next();
                }
                let (radix, str) = if cur.prev().unwrap() == '0' {
                    match cur.next() {
                        Some('b') => (2, take_while!(cur, is_binary_digit)),
                        Some('o') => (8, take_while!(cur, is_octal_digit)),
                        Some('x') => (16, take_while!(cur, is_hex_digit)),
                        _ => {
                            cur.back();
                            cur.back();
                            (10, take_while!(cur, is_decimal_digit))
                        }
                    }
                } else {
                    cur.back();
                    (10, take_while!(cur, is_decimal_digit))
                };

                let n = u32::from_str_radix(str, radix).map_err(|e| {
                    LexError::ParseIntError(if negative {
                        // Map positive overflows to negative ones when the number is negative
                        match e.kind().clone() {
                            IntErrorKind::PosOverflow => IntErrorKind::NegOverflow,
                            o => o,
                        }
                    } else {
                        e.kind().clone()
                    })
                })?;
                // TODO: provide ways to manually specify signed vs unsigned int literals
                if negative {
                    match i32::try_from(n) {
                        Ok(i) => Ok(Token::Literal(LiteralToken::Int(i * -1))),
                        Err(_) => Err(LexError::ParseIntError(IntErrorKind::NegOverflow)),
                    }
                } else {
                    Ok(Token::Literal(LiteralToken::Uint(n)))
                }
            }
            '\'' => {
                let res = match cur.next() {
                    Some('\\') => match cur.next() {
                        Some('t') => Ok(Token::Literal(LiteralToken::Char('\t'))),
                        Some('n') => Ok(Token::Literal(LiteralToken::Char('\n'))),
                        Some('\\') => Ok(Token::Literal(LiteralToken::Char('\\'))),
                        Some(c) => Err(LexError::InvalidCharEscape(c)),
                        None => Err(LexError::UnterminatedChar),
                    },
                    Some(c) => Ok(Token::Literal(LiteralToken::Char(c))),
                    None => Err(LexError::UnterminatedChar),
                };
                if cur.next().ok_or(LexError::UnterminatedChar)? != '\'' {
                    return Err(LexError::NonSingleChar);
                };
                res
            }
            '#' => Ok(Token::Comment(take_while!(cur, |c| !is_newline(c)))),
            '.' => Ok(Token::Dot),
            ',' => Ok(Token::Comma),
            ':' => Ok(Token::Colon),
            '(' => Ok(Token::OpenParen),
            ')' => Ok(Token::CloseParen),
            '$' => Ok(Token::Dollar),
            '\n' | '\u{0085}' | '\u{2029}' => Ok(Token::Newline),

            c if is_whitespace(c) => Ok(Token::Whitespace),

            c if is_ident_start(c) => {
                cur.back();
                Ok(Token::Ident(take_while!(cur, is_ident)))
            }

            _ => Err(LexError::UnexpectedToken(c)),
        })
    })
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
    is_ident_start(c) || is_decimal_digit(c)
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[test]
    fn basic() {
        assert_eq!(
            lex(include_str!("../tests/basic.asm"))
                .map(Result::unwrap)
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
                Token::Literal(LiteralToken::Uint(13)),
                Token::Newline,
                Token::Ident("addi"),
                Token::Dollar,
                Token::Ident("t1"),
                Token::Comma,
                Token::Dollar,
                Token::Ident("zero"),
                Token::Comma,
                Token::Literal(LiteralToken::Uint(26)),
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
            lex("# a comment").map(Result::unwrap).collect::<Vec<_>>(),
            vec![Token::Comment(" a comment")]
        )
    }

    #[test]
    fn int() {
        assert_eq!(
            lex("-5894").map(Result::unwrap).collect::<Vec<_>>(),
            vec![Token::Literal(LiteralToken::Int(-5894))]
        )
    }

    #[test]
    fn uint() {
        assert_eq!(
            lex("5894").map(Result::unwrap).collect::<Vec<_>>(),
            vec![Token::Literal(LiteralToken::Uint(5894))]
        )
    }

    #[test]
    fn negative_overflow() {
        assert_eq!(
            lex("-584654654654654654694")
                .find_map(|r| match r {
                    Ok(_) => None,
                    Err(e) => Some(e),
                })
                .unwrap(),
            LexError::ParseIntError(IntErrorKind::NegOverflow)
        )
    }

    #[test]
    fn positive_overflow() {
        assert_eq!(
            lex("584654654654654654694")
                .find_map(|r| match r {
                    Ok(_) => None,
                    Err(e) => Some(e),
                })
                .unwrap(),
            LexError::ParseIntError(IntErrorKind::PosOverflow)
        )
    }

    #[test]
    fn binary() {
        assert_eq!(
            lex("-0b0100").map(Result::unwrap).collect::<Vec<_>>(),
            vec![Token::Literal(LiteralToken::Int(-4))]
        )
    }

    #[test]
    fn ocatal() {
        assert_eq!(
            lex("-0o0700").map(Result::unwrap).collect::<Vec<_>>(),
            vec![Token::Literal(LiteralToken::Int(-448))]
        )
    }

    #[test]
    fn hex() {
        assert_eq!(
            lex("-0x0AbE").map(Result::unwrap).collect::<Vec<_>>(),
            vec![Token::Literal(LiteralToken::Int(-2750))]
        )
    }
}

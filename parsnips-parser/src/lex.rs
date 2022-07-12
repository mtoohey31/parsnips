use core::{iter, num::IntErrorKind};

#[cfg_attr(test, derive(PartialEq, Eq, Debug))]
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

#[cfg_attr(test, derive(PartialEq, Eq, Debug))]
pub enum LiteralToken<'a> {
    Int(i32),
    Uint(u32),
    Char(char),
    Str(&'a str),
}

#[cfg_attr(test, derive(Debug))]
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
            '0'..='9' => {
                let radix = if cur.prev().unwrap() == '0' {
                    match cur.next() {
                        Some('b') => 2,
                        Some('o') => 8,
                        Some('x') => 16,
                        _ => {
                            cur.back();
                            cur.back();
                            10
                        }
                    }
                } else {
                    cur.back();
                    10
                };

                let n = i64::from_str_radix(take_while!(cur, is_digit), radix)
                    .map_err(|e| LexError::ParseIntError(e.kind().clone()))?;
                // TODO: provide ways to manually specify signed vs unsigned int literals
                if n.is_negative() {
                    if n < i32::MIN as i64 {
                        Err(LexError::ParseIntError(IntErrorKind::NegOverflow))
                    } else {
                        Ok(Token::Literal(LiteralToken::Int(n as i32)))
                    }
                } else {
                    // in this case, we can safely return n as a u32, because a positive i64 will
                    // fit within the size of a u32
                    Ok(Token::Literal(LiteralToken::Uint(n as u32)))
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
fn is_digit(c: char) -> bool {
    // taken from https://github.com/rust-lang/rust/blob/master/compiler/rustc_lexer/src/lib.rs
    matches!(c, '0'..='9')
}

#[inline(always)]
fn is_ident_start(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_')
}

#[inline(always)]
fn is_ident(c: char) -> bool {
    is_ident_start(c) || is_digit(c)
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
}

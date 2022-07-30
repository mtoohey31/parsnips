extern crate alloc;

use alloc::vec::Vec;

use crate::lex::{lex, LexError, LiteralToken, Token};

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct Ast<'a> {
    pub sections: Vec<Section<'a>>,
}

impl Ast<'_> {
    fn new() -> Self {
        Self {
            sections: Vec::new(),
        }
    }
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum Section<'a> {
    Data(Vec<Data<'a>>),
    Text(Vec<Entry<'a>>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum Entry<'a> {
    Label(&'a str, u32),
    Instruction(Instruction<'a>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum Instruction<'a> {
    Add(Argument<'a>, Argument<'a>, Argument<'a>),
    Addi(Argument<'a>, Argument<'a>, Argument<'a>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum Argument<'a> {
    Register(&'a str),
    Literal(&'a str),
    Label(&'a str),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct Data<'a> {
    pub label: &'a str,
    pub value: DataDeclaration,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct DataDeclaration {
    pub r#type: DataType,
    pub value: DataValue,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum DataType {
    Word,
    HalfWord,
    Byte,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum DataValue {
    String,
    Int,
    Uint,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum ParseError<'a> {
    LexError(LexError),
    UnterminatedDirective,
    UnexpectedToken(Token<'a>),
    UnexpectedEOF,
    UnknownDirective(&'a str),
    UnknownInstruction(&'a str),
}

macro_rules! expect {
    ($ti:expr, $t:expr) => {{
        match $ti.next() {
            Some(t) => {
                if $t == t {
                    Ok(())
                } else {
                    Err(ParseError::UnexpectedToken(t))
                }
            }
            None => Err(ParseError::UnexpectedEOF),
        }
    }};
}

macro_rules! skip_whitespace {
    ($ti:expr) => {{
        while let Some(Token::Whitespace) = $ti.peek() {
            $ti.next();
        }
    }};
}

macro_rules! skip_at_least_one_whitespace {
    ($ti:expr) => {{
        match $ti.peek() {
            Some(Token::Whitespace) => Ok(skip_whitespace!($ti)),
            None => Err(ParseError::UnexpectedEOF),
            Some(_) => Err(ParseError::UnexpectedToken($ti.next().unwrap())),
        }
    }};
}

macro_rules! get_arg {
    ($ti:expr) => {{
        match $ti.next().ok_or(ParseError::UnexpectedEOF)? {
            Token::Dollar => {
                let n = $ti.next().ok_or(ParseError::UnexpectedEOF)?;
                if let Token::Ident(s) = n {
                    Ok(Argument::Register(s))
                } else {
                    Err(ParseError::UnexpectedToken(n))
                }
            }
            Token::Literal(LiteralToken::Num { body, .. }) => Ok(Argument::Literal(body)),
            n => Err(ParseError::UnexpectedToken(n)),
        }
    }};
}

macro_rules! get_one_arg {
    ($ti:expr) => {{
        skip_at_least_one_whitespace!($ti)?;
        get_arg!($ti)?
    }};
}

macro_rules! get_two_args {
    ($ti:expr) => {{
        skip_at_least_one_whitespace!($ti)?;
        let one = get_arg!($ti)?;
        skip_whitespace!($ti);
        expect!($ti, Token::Comma)?;
        skip_whitespace!($ti);
        (one, get_arg!($ti)?)
    }};
}

macro_rules! get_three_args {
    ($ti:expr) => {{
        skip_at_least_one_whitespace!($ti)?;
        let one = get_arg!($ti)?;
        skip_whitespace!($ti);
        expect!($ti, Token::Comma)?;
        skip_whitespace!($ti);
        let two = get_arg!($ti)?;
        skip_whitespace!($ti);
        expect!($ti, Token::Comma)?;
        skip_whitespace!($ti);
        (one, two, get_arg!($ti)?)
    }};
}

pub fn parse(input: &str) -> Result<Ast, ParseError> {
    let mut a = Ast::new();
    let mut cs: Option<Section> = None;

    let mut ti = lex(input)
        .map_err(ParseError::LexError)?
        .into_iter()
        .filter(|t| match t {
            Token::Comment(_) => false,
            _ => true,
        })
        .peekable();

    // TODO: wrap the error properly here
    while let Some(t) = ti.next() {
        match t {
            Token::Dot => {
                let tn = ti.next().ok_or(ParseError::UnterminatedDirective)?;
                if let Some(s) = cs.take() {
                    a.sections.push(s);
                }
                match tn {
                    Token::Ident("data") => cs = Some(Section::Data(Vec::new())),
                    Token::Ident("text") => cs = Some(Section::Text(Vec::new())),
                    Token::Ident(d) => return Err(ParseError::UnknownDirective(d)),
                    _ => return Err(ParseError::UnexpectedToken(tn)),
                }
            }
            Token::Comma => todo!(),
            Token::Colon => todo!(),
            Token::OpenParen => todo!(),
            Token::CloseParen => todo!(),
            Token::Dollar => todo!(),
            Token::Whitespace => {}
            Token::Newline => {}
            Token::Ident(i) => {
                match cs.as_mut() {
                    Some(Section::Data(_)) => {
                        // It can only be a label
                    }
                    Some(Section::Text(entries)) => {
                        // We might get a label or an instruction

                        // TODO: this check will break if `syscall` is the last
                        // thing in the file
                        if &Token::Colon == ti.peek().ok_or(ParseError::UnexpectedEOF)? {
                            // This is a label
                        } else {
                            // This is an instruction
                            entries.push(Entry::Instruction(match i {
                                "add" => {
                                    let args = get_three_args!(ti);
                                    Instruction::Add(args.0, args.1, args.2)
                                }
                                "addi" => {
                                    let args = get_three_args!(ti);
                                    Instruction::Addi(args.0, args.1, args.2)
                                }
                                _ => return Err(ParseError::UnknownInstruction(i)),
                            }));
                        }
                    }
                    None => todo!(),
                };
            }
            Token::Literal(_) => todo!(),
            // Shouldn't be possible because we're filtering out comments above
            Token::Comment(_) => panic!(),
        }
    }
    if let Some(s) = cs {
        a.sections.push(s);
    }
    Ok(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        assert_eq!(
            parse(include_str!("../tests/basic.asm")).unwrap(),
            Ast {
                sections: vec![Section::Text(vec![
                    Entry::Instruction(Instruction::Addi(
                        Argument::Register("t0"),
                        Argument::Register("zero"),
                        Argument::Literal("13")
                    )),
                    Entry::Instruction(Instruction::Addi(
                        Argument::Register("t1"),
                        Argument::Register("zero"),
                        Argument::Literal("26")
                    )),
                    Entry::Instruction(Instruction::Add(
                        Argument::Register("t2"),
                        Argument::Register("t0"),
                        Argument::Register("t1")
                    ))
                ])]
            }
        );
    }
}

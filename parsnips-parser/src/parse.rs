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
    Label(&'a str),
    Instruction(Instruction<'a>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct Instruction<'a> {
    name: &'a str,
    arguments: Vec<Argument<'a>>,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum Argument<'a> {
    Register(&'a str),
    OffsetRegister { offset: &'a str, register: &'a str },
    Literal(&'a str),
    Label(&'a str),
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct Data<'a> {
    pub label: &'a str,
    pub value: DataDeclaration<'a>,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub struct DataDeclaration<'a> {
    pub kind: DataKind,
    pub value: DataValue<'a>,
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum DataKind {
    Word,
    HalfWord,
    Byte,
    Asciiz,
}

// TODO: figure out how to return the parse error here, things are kinda funky
// with lifetimes it looks like, maybe I should forget about trying to do it
// with an existing trait.
impl TryFrom<&str> for DataKind {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "word" => Ok(Self::Word),
            "hword" => Ok(Self::HalfWord),
            "byte" => Ok(Self::Byte),
            "asciiz" => Ok(Self::Asciiz),
            _ => Err(()),
        }
    }
}

// TODO: populate the values of this struct
#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub enum DataValue<'a> {
    String(&'a str),
    Int,
    Uint,
    // TODO: make value something other than usize
    Array { value: usize, size: usize },
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
    UnknownDataKind(&'a str),
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

macro_rules! expect_ident {
    ($ti:expr) => {{
        match $ti.next() {
            Some(t) => {
                if let Token::Ident(s) = t {
                    Ok(s)
                } else {
                    Err(ParseError::UnexpectedToken(t))
                }
            }
            None => Err(ParseError::UnexpectedEOF),
        }
    }};
}

macro_rules! expect_literal {
    ($ti:expr) => {{
        match $ti.next() {
            Some(t) => {
                if let Token::Literal(l) = t {
                    Ok(l)
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

pub fn parse(input: &str) -> Result<Ast, ParseError> {
    let mut a = Ast::new();
    let mut cs: Option<Section> = None;

    // TODO: elide comments on a type level, i.e. maybe have a second level of
    // nested enums for whether the token is a comment, and drill down to the
    // set of enums that contain no comments here so we don't have to have
    // panics in match statements for when comments are encountered all over the
    // place.
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
                skip_whitespace!(ti);
                expect!(ti, Token::Newline)?;
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
                    Some(Section::Data(data)) => {
                        // It can only be a label
                        expect!(ti, Token::Colon)?;
                        skip_whitespace!(ti);
                        expect!(ti, Token::Dot)?;
                        let kind_str = expect_ident!(ti)?;
                        let kind: DataKind = DataKind::try_from(kind_str)
                            .or_else(|_| Err(ParseError::UnknownDataKind(kind_str)))?;
                        skip_at_least_one_whitespace!(ti)?;
                        data.push(Data {
                            label: i,
                            value: DataDeclaration {
                                kind,
                                value: match ti.next().ok_or(ParseError::UnexpectedEOF)? {
                                    Token::Dot => todo!(),
                                    Token::Comma => todo!(),
                                    Token::Colon => todo!(),
                                    Token::OpenParen => todo!(),
                                    Token::CloseParen => todo!(),
                                    Token::Dollar => todo!(),
                                    Token::Whitespace => todo!(),
                                    Token::Newline => todo!(),
                                    Token::Ident(_) => todo!(),
                                    Token::Literal(LiteralToken::Num { .. }) => {
                                        skip_whitespace!(ti);
                                        match ti.next() {
                                            None => todo!(),
                                            Some(Token::Dot) => todo!(),
                                            Some(Token::Comma) => todo!(),
                                            Some(Token::Colon) => {
                                                skip_whitespace!(ti);
                                                match expect_literal!(ti)? {
                                                    LiteralToken::Num { .. } => {
                                                        // TODO: translate and populate this
                                                        DataValue::Array { value: 0, size: 0 }
                                                    }
                                                    LiteralToken::Char(_) => todo!(),
                                                    LiteralToken::Str(_) => todo!(),
                                                }
                                            }
                                            Some(Token::OpenParen) => todo!(),
                                            Some(Token::CloseParen) => todo!(),
                                            Some(Token::Dollar) => todo!(),
                                            Some(Token::Whitespace) => todo!(),
                                            Some(Token::Newline) => DataValue::Int,
                                            Some(Token::Ident(_)) => todo!(),
                                            Some(Token::Literal(_)) => todo!(),

                                            Some(Token::Comment(_)) => panic!(),
                                        }
                                    }
                                    Token::Literal(l) => match l {
                                        LiteralToken::Num { .. } => todo!(),
                                        LiteralToken::Char(_) => todo!(),
                                        LiteralToken::Str(s) => DataValue::String(s),
                                    },

                                    Token::Comment(_) => panic!(),
                                },
                            },
                        })
                    }
                    Some(Section::Text(entries)) => {
                        // We might get a label or an instruction

                        // TODO: this check will break if `syscall` is the last
                        // thing in the file
                        if &Token::Colon == ti.peek().ok_or(ParseError::UnexpectedEOF)? {
                            // This is a label
                            ti.next().unwrap();
                            entries.push(Entry::Label(i))
                        } else {
                            // This is an instruction
                            let mut inst = Instruction {
                                name: i,
                                arguments: Vec::new(),
                            };

                            skip_whitespace!(ti);
                            match ti.next() {
                                Some(Token::Newline) | None => {
                                    entries.push(Entry::Instruction(inst));
                                    continue;
                                }
                                Some(Token::Dollar) => {
                                    inst.arguments.push(Argument::Register(expect_ident!(ti)?))
                                }
                                Some(Token::Ident(i)) => {
                                    inst.arguments.push(Argument::Label(i));
                                }
                                Some(Token::Literal(LiteralToken::Num {
                                    negative: _,
                                    kind: _,
                                    body: b,
                                })) => inst.arguments.push(Argument::Literal(b)),
                                Some(Token::Dot) => todo!(),
                                Some(Token::Comma) => todo!(),
                                Some(Token::Colon) => todo!(),
                                Some(Token::OpenParen) => todo!(),
                                Some(Token::CloseParen) => todo!(),
                                Some(Token::Whitespace) => todo!(),
                                Some(Token::Literal(_)) => todo!(),

                                Some(Token::Comment(_)) => panic!(),
                            }

                            loop {
                                skip_whitespace!(ti);
                                match ti.next() {
                                    Some(Token::Comma) => {} // Get next arg
                                    Some(Token::Newline) | None => break,
                                    Some(u) => return Err(ParseError::UnexpectedToken(u)),
                                }
                                skip_whitespace!(ti);
                                match ti.next() {
                                    Some(Token::Dollar) => {
                                        inst.arguments.push(Argument::Register(expect_ident!(ti)?));
                                    }
                                    Some(Token::Ident(i)) => {
                                        inst.arguments.push(Argument::Label(i));
                                    }
                                    Some(Token::Literal(LiteralToken::Num {
                                        negative: _,
                                        kind: _,
                                        body: b,
                                    })) => {
                                        if Some(&Token::OpenParen) == ti.peek() {
                                            ti.next().unwrap();
                                            expect!(ti, Token::Dollar)?;
                                            inst.arguments.push(Argument::OffsetRegister {
                                                offset: b,
                                                register: expect_ident!(ti)?,
                                            });
                                            expect!(ti, Token::CloseParen)?;
                                        } else {
                                            inst.arguments.push(Argument::Literal(b))
                                        }
                                    }
                                    Some(Token::Dot) => todo!(),
                                    Some(Token::Comma) => todo!(),
                                    Some(Token::Colon) => todo!(),
                                    Some(Token::OpenParen) => todo!(),
                                    Some(Token::CloseParen) => todo!(),
                                    Some(Token::Whitespace) => todo!(),
                                    Some(Token::Newline) => todo!(),
                                    Some(Token::Literal(_)) => todo!(),
                                    None => return Err(ParseError::UnexpectedEOF),

                                    Some(Token::Comment(_)) => panic!(),
                                }
                            }

                            entries.push(Entry::Instruction(inst));
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
    use alloc::vec;

    #[test]
    fn basic() {
        assert_eq!(
            parse(include_str!("../tests/basic.asm")).unwrap(),
            Ast {
                sections: vec![Section::Text(vec![
                    Entry::Instruction(Instruction {
                        name: "addi",
                        arguments: vec![
                            Argument::Register("t0"),
                            Argument::Register("zero"),
                            Argument::Literal("13")
                        ],
                    }),
                    Entry::Instruction(Instruction {
                        name: "addi",
                        arguments: vec![
                            Argument::Register("t1"),
                            Argument::Register("zero"),
                            Argument::Literal("26")
                        ],
                    }),
                    Entry::Instruction(Instruction {
                        name: "add",
                        arguments: vec![
                            Argument::Register("t2"),
                            Argument::Register("t0"),
                            Argument::Register("t1")
                        ],
                    })
                ])]
            }
        );
    }

    #[test]
    fn fib() {
        // TODO: update this to include the contents of literals and other
        // missing data
        assert_eq!(
            parse(include_str!("../tests/Fibonacci.asm")).unwrap(),
            Ast {
                sections: vec![
                    Section::Data(vec![
                        Data {
                            label: "fibs",
                            value: DataDeclaration {
                                kind: DataKind::Word,
                                value: DataValue::Array { value: 0, size: 0 }
                            }
                        },
                        Data {
                            label: "size",
                            value: DataDeclaration {
                                kind: DataKind::Word,
                                value: DataValue::Int,
                            }
                        }
                    ]),
                    Section::Text(vec![
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("t0"), Argument::Label("fibs")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("t5"), Argument::Label("size")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("t5"),
                                Argument::OffsetRegister {
                                    offset: "0",
                                    register: "t5"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![Argument::Register("t2"), Argument::Literal("1")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add.d",
                            arguments: vec![
                                Argument::Register("f0"),
                                Argument::Register("f2"),
                                Argument::Register("f4")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "sw",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::OffsetRegister {
                                    offset: "0",
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "sw",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::OffsetRegister {
                                    offset: "4",
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("t5"),
                                Argument::Literal("2")
                            ]
                        }),
                        Entry::Label("loop"),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("t3"),
                                Argument::OffsetRegister {
                                    offset: "0",
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("t4"),
                                Argument::OffsetRegister {
                                    offset: "4",
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::Register("t3"),
                                Argument::Register("t4")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "sw",
                            arguments: vec![
                                Argument::Register("t2"),
                                Argument::OffsetRegister {
                                    offset: "8",
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t0"),
                                Argument::Register("t0"),
                                Argument::Literal("4")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("t1"),
                                Argument::Literal("1")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "bgtz",
                            arguments: vec![Argument::Register("t1"), Argument::Label("loop")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("a0"), Argument::Label("fibs")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("a1"),
                                Argument::Register("zero"),
                                Argument::Register("t5")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "jal",
                            arguments: vec![Argument::Label("print")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![Argument::Register("v0"), Argument::Literal("10")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        })
                    ]),
                    Section::Data(vec![
                        Data {
                            label: "space",
                            value: DataDeclaration {
                                kind: DataKind::Asciiz,
                                value: DataValue::String(" ")
                            }
                        },
                        Data {
                            label: "head",
                            value: DataDeclaration {
                                kind: DataKind::Asciiz,
                                value: DataValue::String("The Fibonacci numbers are:\\n")
                            }
                        }
                    ]),
                    Section::Text(vec![
                        Entry::Label("print"),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("t0"),
                                Argument::Register("zero"),
                                Argument::Register("a0")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "add",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("zero"),
                                Argument::Register("a1")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("a0"), Argument::Label("head")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![Argument::Register("v0"), Argument::Literal("4")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        }),
                        Entry::Label("out"),
                        Entry::Instruction(Instruction {
                            name: "lw",
                            arguments: vec![
                                Argument::Register("a0"),
                                Argument::OffsetRegister {
                                    offset: "0",
                                    register: "t0"
                                }
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![Argument::Register("v0"), Argument::Literal("1")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        }),
                        Entry::Instruction(Instruction {
                            name: "la",
                            arguments: vec![Argument::Register("a0"), Argument::Label("space")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "li",
                            arguments: vec![Argument::Register("v0"), Argument::Literal("4")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "syscall",
                            arguments: vec![]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t0"),
                                Argument::Register("t0"),
                                Argument::Literal("4")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "addi",
                            arguments: vec![
                                Argument::Register("t1"),
                                Argument::Register("t1"),
                                Argument::Literal("1")
                            ]
                        }),
                        Entry::Instruction(Instruction {
                            name: "bgtz",
                            arguments: vec![Argument::Register("t1"), Argument::Label("out")]
                        }),
                        Entry::Instruction(Instruction {
                            name: "jr",
                            arguments: vec![Argument::Register("ra")]
                        })
                    ])
                ]
            }
        );
    }
}

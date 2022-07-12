use crate::lex::Token;

pub struct Ast<'a> {
    sections: &'a [Section<'a>],
}

pub enum Section<'a> {
    Data(&'a [Data<'a>]),
    Text {
        labels: &'a [(&'a str, u32)],
        instructions: &'a [Instruction],
    },
}

pub enum Instruction {}

pub struct Data<'a> {
    label: &'a str,
    value: DataDeclaration,
}

pub struct DataDeclaration {
    r#type: DataType,
    value: DataValue,
}

pub enum DataType {
    Word,
    HalfWord,
    Byte,
}

pub enum DataValue {
    String,
    Int,
    Uint,
}

pub fn parse<'a>(tokens: impl Iterator<Item = Token<'a>>) -> Ast<'a> {
    Ast { sections: &[] }
}

#[cfg(test)]
mod tests {}

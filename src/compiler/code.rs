use std::{
    convert::From,
    collections::HashMap,
    ops::Index,
};

use byteorder::{BigEndian, WriteBytesExt};

use crate::error::Error;

type Result<T> = std::result::Result<T, Error>;

pub type Instructions = Vec<u8>;
pub type Operand = Vec<isize>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum Opcode {
    OpConstant,
}

#[derive(Clone)]
pub struct Definition {
    name: String,
    operand_widths: Vec<u8>,
}

pub struct MCode {
    definitions: HashMap<Opcode, Definition>,
}

impl MCode {
    pub fn new() -> Self {
        let definitions = HashMap::from([
            (Opcode::OpConstant, Definition { name: "Opconstant".to_string(), operand_widths: vec![2] }),
        ]);

        Self {
            definitions,
        }
    }

    pub fn lookup(&self, op: &Opcode) -> Result<Definition> {
        match self.definitions.get(op) {
            Some(x) => Ok(x.clone()),
            None => Err(Error::new(format!("opcode {:?} undefined", op))),
        }
    }

    pub fn make(&self, op: &Opcode, operands: &Operand) -> Instructions {
        let mut instruction = vec![];
        let def = match self.definitions.get(op) {
            Some(x) => x,
            None => return instruction,
        };

        instruction.push(*op as u8);

        for (i, o) in operands.iter().enumerate() {
            match def.operand_widths.get(i) {
                Some(2) => {
                    match instruction.write_u16::<BigEndian>(*o as u16) {
                        Ok(_) => {},
                        Err(_) => return vec![],
                    };
                },
                Some(_) => return vec![],
                None => return vec![],
            };
        };

        instruction
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make(op: &Opcode, operands: &Operand) -> Instructions {
        MCode::new().make(op, operands)
    }

    #[test]
    fn test_make() -> Result<()> {
        let tests = vec![
            (Opcode::OpConstant, vec![65534], [Opcode::OpConstant as u8, 255, 254]),
        ];

        for tt in tests {
            let instruction = make(&tt.0, &tt.1);

            assert_eq!(tt.2.len(), instruction.len());

            for (i, b) in tt.2.iter().enumerate() {
                assert_eq!(*b, instruction[i]);
            };
        };

        Ok(())
    }
}

use std::{
    convert::From,
    collections::HashMap,
    ops::Index,
};

use byteorder::{ByteOrder, BigEndian};

use crate::error::Error;

type Result<T> = std::result::Result<T, Error>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
enum Instruction {
    Empty,
    Three([u8; 3]),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
enum Operand {
    U16(u16),
}

impl From<u16> for Operand {
    fn from(item: u16) -> Self {
        Operand::U16(item)
    }
}

impl From<Operand> for u16 {
    fn from(item: Operand) -> Self {
        match item {
            Operand::U16(x) => x,
        }
    }
}

impl Instruction {
    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Three(_) => 3,
        }
    }
}

impl Index<usize> for Instruction {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            Self::Empty => &0,
            Self::Three(x) => &x[index],
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum Opcode {
    OpConstant,
}

#[derive(Clone)]
pub struct Definition {
    name: String,
    operand_widths: Vec<u8>,
}

struct MCode {
    definitions: HashMap<Opcode, Definition>,
}

impl MCode {
    fn new() -> Self {
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

    pub fn make(&self, op: &Opcode, operands: &[Operand]) -> Instruction {
        let def = match self.definitions.get(op) {
            Some(x) => x,
            None => return Instruction::Empty,
        };

        let mut instruction_len = 1;

        for w in &def.operand_widths {
            instruction_len += w;
        };

        match instruction_len {
            3 => {
                let mut instruction = [0u8; 3];
                instruction[0] = *op as u8;

                for (i, o) in operands.iter().enumerate() {
                    match def.operand_widths.get(i) {
                        Some(2) => {
                            BigEndian::write_u16(&mut instruction[1..], (*o).into());
                        },
                        Some(_) => return Instruction::Empty,
                        None => return Instruction::Empty,
                    };

                };

                Instruction::Three(instruction)
            },
            _ => Instruction::Empty,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make(op: &Opcode, operands: &[Operand]) -> Instruction {
        MCode::new().make(op, operands)
    }

    #[test]
    fn test_make() -> Result<()> {
        let tests = vec![
            (Opcode::OpConstant, [Operand::from(65534u16)], [Opcode::OpConstant as u8, 255, 254]),
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

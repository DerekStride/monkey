use std::{
    convert::From,
    collections::HashMap,
};

use byteorder::{ByteOrder, BigEndian, WriteBytesExt};

use crate::error::{Result, Error};

pub type Instructions = Vec<u8>;
pub type Operand = Vec<isize>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum Opcode {
    OpConstant,
    OpAdd,
}

#[derive(Clone)]
pub struct Definition {
    pub name: String,
    pub op: Opcode,
    pub operand_widths: Vec<u8>,
}

pub struct MCode {
    definitions: HashMap<u8, Definition>,
}

impl MCode {
    pub fn new() -> Self {
        let definitions = HashMap::from([
            (Opcode::OpConstant as u8, Definition { name: "Opconstant".to_string(), op: Opcode::OpConstant, operand_widths: vec![2] }),
            (Opcode::OpAdd as u8, Definition { name: "OpAdd".to_string(), op: Opcode::OpAdd, operand_widths: vec![] }),
        ]);

        Self {
            definitions,
        }
    }

    pub fn lookup(&self, op: &u8) -> Result<Definition> {
        match self.definitions.get(op) {
            Some(x) => Ok(x.clone()),
            None => Err(Error::new(format!("opcode {:?} undefined", op))),
        }
    }

    pub fn make(&self, op: &Opcode, operands: &Operand) -> Instructions {
        let mut instruction = vec![];
        let def = match self.definitions.get(&(*op as u8)) {
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

    pub fn format(&self, ins: &Instructions) -> String {
        let mut buf = String::new();

        let mut i = 0;
        while i < ins.len() {
            let def = match self.lookup(&ins[i]) {
                Ok(x) => x,
                Err(e) => {
                    buf.push_str("ERROR: ");
                    buf.push_str(&e.to_string());
                    buf.push_str("\n");
                    continue;
                },
            };

            let (operands, read) = match MCode::read_operands(&def, &ins[i+1..]) {
                Ok(x) => x,
                Err(e) => {
                    buf.push_str("ERROR: ");
                    buf.push_str(&e.to_string());
                    buf.push_str("\n");
                    continue;
                },
            };

            buf.push_str(&format!("{:0>4} {}\n", i, MCode::format_ins(&def, &operands)));

            i += 1 + read;
        };

        buf
    }

    fn format_ins(def: &Definition, operands: &Operand) -> String {
        let mut buf = String::new();
        let op_count = def.operand_widths.len();

        if op_count != operands.len() {
            buf.push_str(&format!("ERROR: operand len {} does not match defined {}\n", operands.len(), op_count));
            return buf;
        };

        match op_count {
            0 => buf.push_str(&format!("{}", def.name)),
            1 => buf.push_str(&format!("{} {}", def.name, operands.get(0).unwrap())),
            _ => buf.push_str(&format!("ERROR: unhandled operand count ({}) for {}\n", op_count, def.name)),
        }

        buf
    }

    pub fn read_operands(def: &Definition, ins: &[u8]) -> Result<(Operand, usize)> {
        let mut operands = Vec::new();
        let mut offset = 0;

        for (i, width) in def.operand_widths.iter().enumerate() {
            match width {
                2 => operands.insert(i, BigEndian::read_u16(&ins[offset..]) as isize),
                _  => return Err(Error::new(format!("No support for operands of width={}", width))),
            }
            offset += *width as usize;
        };

        Ok((operands, offset))
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
            (Opcode::OpAdd, vec![], vec![Opcode::OpAdd as u8]),
            (Opcode::OpConstant, vec![65534], vec![Opcode::OpConstant as u8, 255, 254]),
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

    #[test]
    fn test_read_operands() -> Result<()> {
        let tests = vec![
            (Opcode::OpConstant, vec![65534], 2),
        ];

        let mcode = MCode::new();

        for tt in tests {
            let instruction = make(&tt.0, &tt.1);
            let def = mcode.lookup(&(tt.0 as u8))?;

            let (operands_read, n) = MCode::read_operands(&def, &instruction[1..])?;

            assert_eq!(tt.2, n);
            assert_eq!(tt.1, operands_read);
        };

        Ok(())
    }

    #[test]
    fn test_fmt_display() -> Result<()> {
        let instructions = vec![
            make(&Opcode::OpConstant, &vec![1]),
            make(&Opcode::OpConstant, &vec![2]),
            make(&Opcode::OpAdd, &vec![]),
            make(&Opcode::OpConstant, &vec![65535]),
        ];

        let expected = vec![
            "0000 Opconstant 1\n",
            "0003 Opconstant 2\n",
            "0006 OpAdd\n",
            "0007 Opconstant 65535\n",
        ].join("");

        let actual_ins: Instructions = instructions
            .into_iter()
            .flatten()
            .collect();

        let actual = MCode::new().format(&actual_ins);
        assert_eq!(expected, actual, "\nexpected:\n{}\nactual:\n{}\n", expected, actual);

        Ok(())
    }
}

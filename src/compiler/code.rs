use std::{
    convert::From,
    collections::HashMap,
};

use byteorder::{ByteOrder, BigEndian, WriteBytesExt};

use crate::error::{Result, Error};

pub type Instructions = Vec<u8>;
pub type Operand = Vec<isize>;
pub type Opcode = u8;

pub const OP_CONSTANT: u8    = 0;
pub const OP_POP: u8         = 1;
pub const OP_ADD: u8         = 2;
pub const OP_SUB: u8         = 3;
pub const OP_MUL: u8         = 4;
pub const OP_DIV: u8         = 5;
pub const OP_TRUE: u8        = 6;
pub const OP_FALSE: u8       = 7;
pub const OP_EQUAL: u8              = 8;
pub const OP_NOT_EQUAL: u8          = 9;
pub const OP_GREATER_THAN: u8       = 10;
pub const OP_MINUS: u8              = 11;
pub const OP_BANG: u8               = 12;
pub const OP_JUMP_NOT_TRUE: u8      = 13;
pub const OP_JUMP: u8               = 14;
pub const OP_NULL: u8               = 15;
pub const OP_SET_GLOBAL: u8         = 16;
pub const OP_GET_GLOBAL: u8         = 17;

#[derive(Clone)]
pub struct Definition {
    pub name: String,
    pub operand_widths: Vec<u8>,
}

pub struct MCode {
    definitions: HashMap<u8, Definition>,
}

impl MCode {
    pub fn new() -> Self {
        let definitions = HashMap::from([
            (OP_CONSTANT, Definition { name: "OpConstant".to_string(), operand_widths: vec![2] }),
            (OP_POP, Definition { name: "OpPop".to_string(), operand_widths: vec![] }),
            (OP_ADD, Definition { name: "OpAdd".to_string(), operand_widths: vec![] }),
            (OP_SUB, Definition { name: "OpSub".to_string(), operand_widths: vec![] }),
            (OP_MUL, Definition { name: "OpMul".to_string(), operand_widths: vec![] }),
            (OP_DIV, Definition { name: "OpDiv".to_string(), operand_widths: vec![] }),
            (OP_TRUE, Definition { name: "OpTrue".to_string(), operand_widths: vec![] }),
            (OP_FALSE, Definition { name: "OpFalse".to_string(), operand_widths: vec![] }),
            (OP_EQUAL, Definition { name: "OpEqual".to_string(), operand_widths: vec![] }),
            (OP_NOT_EQUAL, Definition { name: "OpNotEqual".to_string(), operand_widths: vec![] }),
            (OP_GREATER_THAN, Definition { name: "OpGreatherThan".to_string(), operand_widths: vec![] }),
            (OP_MINUS, Definition { name: "OpMinus".to_string(), operand_widths: vec![] }),
            (OP_BANG, Definition { name: "OpBang".to_string(), operand_widths: vec![] }),
            (OP_JUMP_NOT_TRUE, Definition { name: "OpJumpNotTrue".to_string(), operand_widths: vec![2] }),
            (OP_JUMP, Definition { name: "OpJump".to_string(), operand_widths: vec![2] }),
            (OP_NULL, Definition { name: "OpNull".to_string(), operand_widths: vec![] }),
            (OP_SET_GLOBAL, Definition { name: "OpSetGlobal".to_string(), operand_widths: vec![2] }),
            (OP_GET_GLOBAL, Definition { name: "OpGetGlobal".to_string(), operand_widths: vec![2] }),
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
        let def = match self.definitions.get(op) {
            Some(x) => x,
            None => return instruction,
        };

        instruction.push(*op);

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
            (OP_ADD, vec![], vec![OP_ADD]),
            (OP_POP, vec![], vec![OP_POP]),
            (OP_CONSTANT, vec![65534], vec![OP_CONSTANT, 255, 254]),
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
            (OP_CONSTANT, vec![65534], 2),
            (OP_POP, vec![], 0),
        ];

        let mcode = MCode::new();

        for tt in tests {
            let instruction = make(&tt.0, &tt.1);
            let def = mcode.lookup(&tt.0)?;

            let (operands_read, n) = MCode::read_operands(&def, &instruction[1..])?;

            assert_eq!(tt.2, n);
            assert_eq!(tt.1, operands_read);
        };

        Ok(())
    }

    #[test]
    fn test_fmt_display() -> Result<()> {
        let instructions = vec![
            make(&OP_CONSTANT, &vec![1]),
            make(&OP_CONSTANT, &vec![2]),
            make(&OP_ADD, &vec![]),
            make(&OP_CONSTANT, &vec![65535]),
        ];

        let expected = vec![
            "0000 OpConstant 1\n",
            "0003 OpConstant 2\n",
            "0006 OpAdd\n",
            "0007 OpConstant 65535\n",
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

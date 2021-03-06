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
pub const OP_ARRAY: u8              = 18;
pub const OP_HASH: u8               = 19;
pub const OP_INDEX: u8              = 20;
pub const OP_CALL: u8               = 21;
pub const OP_RETURN: u8             = 22;
pub const OP_RETURN_VAL: u8         = 23;
pub const OP_SET_LOCAL: u8          = 24;
pub const OP_GET_LOCAL: u8          = 25;
pub const OP_GET_BUILTIN: u8        = 26;
pub const OP_CLOSURE: u8            = 27;
pub const OP_GET_FREE: u8           = 28;
pub const OP_CURRENT_CLOSURE: u8    = 29;

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
            (OP_ARRAY, Definition { name: "OpArray".to_string(), operand_widths: vec![2] }),
            (OP_HASH, Definition { name: "OpHash".to_string(), operand_widths: vec![2] }),
            (OP_INDEX, Definition { name: "OpIndex".to_string(), operand_widths: vec![] }),
            (OP_CALL, Definition { name: "OpCall".to_string(), operand_widths: vec![1] }),
            (OP_RETURN, Definition { name: "OpReturn".to_string(), operand_widths: vec![] }),
            (OP_RETURN_VAL, Definition { name: "OpReturnVal".to_string(), operand_widths: vec![] }),
            (OP_SET_LOCAL, Definition { name: "OpSetLocal".to_string(), operand_widths: vec![1] }),
            (OP_GET_LOCAL, Definition { name: "OpGetLocal".to_string(), operand_widths: vec![1] }),
            (OP_GET_BUILTIN, Definition { name: "OpGetBuiltin".to_string(), operand_widths: vec![1] }),
            (OP_CLOSURE, Definition { name: "OpClosure".to_string(), operand_widths: vec![2, 1] }),
            (OP_GET_FREE, Definition { name: "OpGetFree".to_string(), operand_widths: vec![1] }),
            (OP_CURRENT_CLOSURE, Definition { name: "OpCurrentClosure".to_string(), operand_widths: vec![] }),
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
                Some(1) => instruction.push(*o as u8),
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

    pub fn format(&self, ins: &[u8]) -> String {
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
            1 => buf.push_str(&format!("{} {}", def.name, operands[0])),
            2 => buf.push_str(&format!("{} {} {}", def.name, operands[0], operands[1])),
            _ => buf.push_str(&format!("ERROR: unhandled operand count ({}) for {}\n", op_count, def.name)),
        }

        buf
    }

    pub fn read_operands(def: &Definition, ins: &[u8]) -> Result<(Operand, usize)> {
        let mut operands = Vec::new();
        let mut offset = 0;

        for (i, width) in def.operand_widths.iter().enumerate() {
            match width {
                1 => operands.insert(i, ins[offset] as isize),
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
            (OP_SET_LOCAL, vec![254], vec![OP_SET_LOCAL, 254]),
            (OP_GET_LOCAL, vec![122], vec![OP_GET_LOCAL, 122]),
            (OP_CLOSURE, vec![65534, 253], vec![OP_CLOSURE, 255, 254, 253]),
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
            (OP_GET_LOCAL, vec![122], 1),
            (OP_CLOSURE, vec![65534, 253], 3),
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
            make(&OP_SET_LOCAL, &vec![254]),
            make(&OP_CLOSURE, &vec![65535, 254]),
        ];

        let expected = vec![
            "0000 OpConstant 1\n",
            "0003 OpConstant 2\n",
            "0006 OpAdd\n",
            "0007 OpConstant 65535\n",
            "0010 OpSetLocal 254\n",
            "0012 OpClosure 65535 254\n",
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

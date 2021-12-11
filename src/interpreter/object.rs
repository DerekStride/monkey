#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
struct Integer {
    pub value: i128,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
struct Boolean {
    pub value: bool,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum MObject {
    Int(Integer),
    Bool(Boolean),
    Null,
}

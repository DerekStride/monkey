#[macro_export]
macro_rules! mhash {
    () => ({
        $crate::interpreter::object::MObject::Hash(
            $crate::interpreter::object::MHash {
                pairs: std::collections::HashMap::new()
            }
        )
    });

    ( $( ($k:expr, $v:expr) ),*) => ({
        let mut pairs = std::collections::HashMap::new();

        $(
            let key = match $k.clone() {
                $crate::interpreter::object::MObject::Str(x) => $crate::interpreter::object::HashKey::Str(x),
                $crate::interpreter::object::MObject::Int(x) => $crate::interpreter::object::HashKey::Int(x),
                $crate::interpreter::object::MObject::Bool(x) => $crate::interpreter::object::HashKey::Bool(x),
                _ => panic!("Expected key to be Int, Str, or Bool. Got: {:?}", $k),
            };

            let pair = $crate::interpreter::object::HashPair {
                key: $k,
                value: $v,
            };

            pairs.insert(key, pair);
        )*

        $crate::interpreter::object::MObject::Hash(
            $crate::interpreter::object::MHash {
                pairs,
            }
        )
    });

    ( $( ($k:expr, $v:expr) ),* ,) => ({
        mhash![ $( ($k, $v) ), * ]
    });
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use crate::{test_utils::*, interpreter::object::*};

    #[test]
    fn test_emtyp_mhash() {
        let expected = MObject::Hash(
            MHash {
                pairs: HashMap::new(),
            }
        );

        let actual = mhash![];

        assert_eq!(expected, actual);
    }
    #[test]
    fn test_mhash() {
        let expected = MObject::Hash(
            MHash {
                pairs: HashMap::from([
                    (HashKey::Int(Integer { value: 1 }), HashPair { key: i_to_o(1), value: i_to_o(2) }),
                    (HashKey::Int(Integer { value: 3 }), HashPair { key: i_to_o(3), value: i_to_o(4) }),
                ]),
            }
        );

        let actual = mhash![
            (i_to_o(1), i_to_o(2)),
            (i_to_o(3), i_to_o(4)),
        ];

        assert_eq!(expected, actual);
    }
}

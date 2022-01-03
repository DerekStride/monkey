#[macro_export]
macro_rules! mhash {
    () => ({
        $crate::object::MObject::Hash(
            $crate::object::MHash {
                pairs: std::collections::HashMap::new()
            }
        )
    });

    ( $( ($k:expr, $v:expr) ),*) => ({
        let mut pairs = std::collections::HashMap::new();

        $(
            let key = match $k.clone() {
                $crate::object::MObject::Str(x) => $crate::object::HashKey::Str(x),
                $crate::object::MObject::Int(x) => $crate::object::HashKey::Int(x),
                $crate::object::MObject::Bool(x) => $crate::object::HashKey::Bool(x),
                _ => panic!("Expected key to be Int, Str, or Bool. Got: {:?}", $k),
            };

            let pair = $crate::object::HashPair {
                key: $k,
                value: $v,
            };

            pairs.insert(key, pair);
        )*

        $crate::object::MObject::Hash(
            $crate::object::MHash {
                pairs,
            }
        )
    });

    ( $( ($k:expr, $v:expr) ),* ,) => ({
        mhash![ $( ($k, $v) ), * ]
    });
}

#[macro_export]
macro_rules! mvec {
    () => ({
        $crate::object::MObject::Array(
            $crate::object::MArray {
                elements: std::vec::Vec::new()
            }
        )
    });

    ( $( $elem:expr ),*) => ({
        let elements = vec![ $( $elem ), * ];

        $crate::object::MObject::Array(
            $crate::object::MArray {
                elements,
            }
        )
    });

    ( $( $elem:expr ),* ,) => ({
        mvec![ $( $elem ), * ]
    });
}

#[macro_export]
macro_rules! merr {
    ( $value:expr ) => ({
        $crate::object::MObject::Err(
            $crate::object::MError {
                value: $value.to_string()
            }
        )
    });
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use crate::{test_utils::*, object::*};

    #[test]
    fn test_empty_mhash() {
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

    #[test]
    fn test_empty_mvec() {
        let expected = MObject::Array(
            MArray {
                elements: Vec::new(),
            }
        );

        let actual = mvec![];

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_mvec() {
        let expected = MObject::Array(
            MArray {
                elements: vec![i_to_o(1), i_to_o(2), i_to_o(3)],
            }
        );

        let actual = mvec![
            i_to_o(1),
            i_to_o(2),
            i_to_o(3),
        ];

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_merr() {
        let expected = MObject::Err(
            MError {
                value: "arguments to `first` must be ARRAY, got 1".to_string(),
            }
        );

        let actual = merr!("arguments to `first` must be ARRAY, got 1");

        assert_eq!(expected, actual);
    }
}

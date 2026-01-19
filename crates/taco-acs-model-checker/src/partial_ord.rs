//! Custom Partial Order Trait
//!
//! This module defines a new `PartialOrdering` trait which is different to the
//! standard libraries `PartialOrd` trait.
//! The reason is to allow for a more flexible definition of what a partial
//! order is and how it behaves on different objects.

use core::fmt;
use std::{collections::HashMap, hash::Hash};

/// Result of a comparison in a partial order between an object `a` and `b`
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(i8)]
pub enum PartialOrdCompResult {
    /// Two given objects are incomparable
    Incomparable,
    /// First object is smaller than the second one
    Smaller,
    /// Both objects are equal
    Equal,
    /// First object is greater than the second one
    Greater,
}

impl PartialOrdCompResult {
    #[inline(always)]
    pub fn combine(self, other: Self) -> Self {
        match (self, other) {
            (PartialOrdCompResult::Incomparable, _)
            | (_, PartialOrdCompResult::Incomparable)
            | (PartialOrdCompResult::Smaller, PartialOrdCompResult::Greater)
            | (PartialOrdCompResult::Greater, PartialOrdCompResult::Smaller) => {
                PartialOrdCompResult::Incomparable
            }

            (PartialOrdCompResult::Smaller, PartialOrdCompResult::Smaller)
            | (PartialOrdCompResult::Smaller, PartialOrdCompResult::Equal)
            | (PartialOrdCompResult::Equal, PartialOrdCompResult::Smaller) => {
                PartialOrdCompResult::Smaller
            }
            (PartialOrdCompResult::Equal, PartialOrdCompResult::Equal) => {
                PartialOrdCompResult::Equal
            }
            (PartialOrdCompResult::Greater, PartialOrdCompResult::Greater)
            | (PartialOrdCompResult::Equal, PartialOrdCompResult::Greater)
            | (PartialOrdCompResult::Greater, PartialOrdCompResult::Equal) => {
                PartialOrdCompResult::Greater
            }
        }
    }
}

impl fmt::Display for PartialOrdCompResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PartialOrdCompResult::Incomparable => write!(f, "≠"),
            PartialOrdCompResult::Smaller => write!(f, "<"),
            PartialOrdCompResult::Equal => write!(f, "=="),
            PartialOrdCompResult::Greater => write!(f, ">"),
        }
    }
}

/// Trait for types implementing a partial order
///
/// This trait allows you to specify a custom partial order that does not
/// conflict with the standard [`PartialOrd`] trait.
pub trait PartialOrder {
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult;

    /// Check whether `self` is greater or equal to `other` in the partial order
    fn is_greater_or_equal(&self, other: &Self) -> bool {
        matches!(
            self.part_cmp(other),
            PartialOrdCompResult::Equal | PartialOrdCompResult::Greater
        )
    }

    /// Check whether `self` is smaller or equal to `other` in the partial order
    fn is_smaller_or_equal(&self, other: &Self) -> bool {
        matches!(
            self.part_cmp(other),
            PartialOrdCompResult::Equal | PartialOrdCompResult::Smaller
        )
    }
}

macro_rules! impl_partial_order {
    ( $( $ty:ty )* ) => {
        $(
            impl PartialOrder for $ty {
                fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
                    match self.partial_cmp(other) {
                        Some(res) => match res {
                            std::cmp::Ordering::Less => PartialOrdCompResult::Smaller,
                            std::cmp::Ordering::Equal => PartialOrdCompResult::Equal,
                            std::cmp::Ordering::Greater => PartialOrdCompResult::Greater,
                        },
                        None => PartialOrdCompResult::Incomparable,
                    }
                }
            }
        )*
    };
}

impl_partial_order!(usize i8 u8 i16 u16 i32 u32 i64 u64 i128 u128);

impl<T: PartialOrder> PartialOrder for Vec<T> {
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
        // all vectors which don't have equal length are considered incomparable
        if self.len() != other.len() {
            return PartialOrdCompResult::Incomparable;
        }

        let mut res = PartialOrdCompResult::Equal;
        for (self_item, other_item) in self.iter().zip(other.iter()) {
            let cmp = self_item.part_cmp(other_item);
            res = res.combine(cmp);

            if res == PartialOrdCompResult::Incomparable {
                break;
            }
        }

        res
    }
}

impl<V: PartialOrder, K: Hash + Eq> PartialOrder for HashMap<K, V> {
    fn part_cmp(&self, other: &Self) -> PartialOrdCompResult {
        // all HashMaps which don't have equal length will have at least one incomparable element
        if self.len() != other.len() {
            return PartialOrdCompResult::Incomparable;
        }

        let mut res = PartialOrdCompResult::Equal;
        for (self_key, self_val) in self.iter() {
            let other_val = other.get(self_key);
            if other_val.is_none() {
                return PartialOrdCompResult::Incomparable;
            }

            let cmp = self_val.part_cmp(other_val.unwrap());
            res = res.combine(cmp);

            if res == PartialOrdCompResult::Incomparable {
                break;
            }
        }

        res
    }
}

/// Set of configurations where each element is incomparable to every other
/// element in the set
///
/// Each configuration represents an upwards closed set of configurations, where
/// each of the configurations contained is the minimal basis of the set of
/// configurations it represents.
#[derive(Debug, Clone, PartialEq)]
pub struct SetMinimalBasis<T: PartialOrder + PartialEq + Hash + Eq> {
    configs: Vec<T>,
}

impl<T: PartialOrder + PartialEq + Hash + Eq> SetMinimalBasis<T> {
    /// Create a new set of minimal basis
    ///
    /// If there are comparable elements only the smaller one will be maintained
    /// in the set.
    pub fn new<V: Into<Vec<T>>>(configs: V) -> Self {
        let configs = configs.into();
        if configs.len() <= 1 {
            return Self { configs };
        }

        let mut reduced_set = Vec::new();
        for cfg in configs.into_iter() {
            // configuration is greater than some already inserted configuration, skip
            if reduced_set
                .iter()
                .any(|existing_cfg: &T| cfg.is_greater_or_equal(existing_cfg))
            {
                continue;
            }

            // remove elements that are bigger than the element we want to insert
            reduced_set.retain(|existing_cf| !existing_cf.is_greater_or_equal(&cfg));

            reduced_set.push(cfg);
        }

        Self {
            configs: reduced_set,
        }
    }

    /// Retain only the elements for which `f` returns true
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.configs.retain(f);
    }
}

impl<T: PartialOrder + PartialEq + Hash + Eq, I: Iterator<Item = T>> From<I>
    for SetMinimalBasis<T>
{
    fn from(value: I) -> Self {
        SetMinimalBasis::new(value.into_iter().collect::<Vec<_>>())
    }
}

impl<T: PartialOrder + PartialEq + Hash + Eq> IntoIterator for SetMinimalBasis<T> {
    type Item = T;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.configs.into_iter()
    }
}

impl<'a, T: PartialOrder + PartialEq + Hash + Eq> IntoIterator for &'a SetMinimalBasis<T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.configs.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::partial_ord::{PartialOrdCompResult, PartialOrder, SetMinimalBasis};

    #[test]
    fn test_combine() {
        let a = PartialOrdCompResult::Incomparable;
        let b = PartialOrdCompResult::Incomparable;
        assert_eq!(a.combine(b), PartialOrdCompResult::Incomparable);

        let a = PartialOrdCompResult::Incomparable;
        let b = PartialOrdCompResult::Smaller;
        assert_eq!(a.combine(b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.combine(a), PartialOrdCompResult::Incomparable);

        let a = PartialOrdCompResult::Incomparable;
        let b = PartialOrdCompResult::Equal;
        assert_eq!(a.combine(b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.combine(a), PartialOrdCompResult::Incomparable);

        let a = PartialOrdCompResult::Incomparable;
        let b = PartialOrdCompResult::Greater;
        assert_eq!(a.combine(b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.combine(a), PartialOrdCompResult::Incomparable);

        let a = PartialOrdCompResult::Smaller;
        let b = PartialOrdCompResult::Smaller;
        assert_eq!(a.combine(b), PartialOrdCompResult::Smaller);
        assert_eq!(b.combine(a), PartialOrdCompResult::Smaller);

        let a = PartialOrdCompResult::Smaller;
        let b = PartialOrdCompResult::Equal;
        assert_eq!(a.combine(b), PartialOrdCompResult::Smaller);
        assert_eq!(b.combine(a), PartialOrdCompResult::Smaller);

        let a = PartialOrdCompResult::Smaller;
        let b = PartialOrdCompResult::Greater;
        assert_eq!(a.combine(b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.combine(a), PartialOrdCompResult::Incomparable);

        let a = PartialOrdCompResult::Equal;
        let b = PartialOrdCompResult::Equal;
        assert_eq!(a.combine(b), PartialOrdCompResult::Equal);
        assert_eq!(b.combine(a), PartialOrdCompResult::Equal);

        let a = PartialOrdCompResult::Equal;
        let b = PartialOrdCompResult::Greater;
        assert_eq!(a.combine(b), PartialOrdCompResult::Greater);
        assert_eq!(b.combine(a), PartialOrdCompResult::Greater);

        let a = PartialOrdCompResult::Greater;
        let b = PartialOrdCompResult::Greater;
        assert_eq!(a.combine(b), PartialOrdCompResult::Greater);
        assert_eq!(b.combine(a), PartialOrdCompResult::Greater);
    }

    #[test]
    fn test_vecs_equal() {
        let a = vec![1, 2, 3, 4, 5];
        let b = vec![1, 2, 3, 4, 5];

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Equal);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Equal);

        assert!(a.is_greater_or_equal(&b));
        assert!(b.is_greater_or_equal(&a));

        assert!(a.is_smaller_or_equal(&b));
        assert!(b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_vecs_different_size() {
        let a = vec![1, 2];
        let b = vec![1];

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Incomparable);

        assert!(!a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(!b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_vecs_gt_one() {
        let a = vec![1, 4, 3, 4, 5];
        let b = vec![1, 2, 3, 4, 5];

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Greater);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Smaller);

        assert!(a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_vecs_gt_all() {
        let a = vec![2, 4, 6, 8, 10];
        let b = vec![1, 2, 3, 4, 5];

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Greater);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Smaller);

        assert!(a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_vecs_one_gt_on_lt() {
        let a = vec![2, 1, 3, 4, 5];
        let b = vec![1, 2, 3, 4, 5];

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Incomparable);

        assert!(!a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(!b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_hm_equal() {
        let a = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let b = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Equal);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Equal);

        assert!(a.is_greater_or_equal(&b));
        assert!(b.is_greater_or_equal(&a));

        assert!(a.is_smaller_or_equal(&b));
        assert!(b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_hm_different_size() {
        let a = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let b = HashMap::from([("a", 1), ("b", 2)]);

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Incomparable);

        assert!(!a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(!b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_hm_gt_one() {
        let a = HashMap::from([("a", 1), ("b", 3), ("c", 3)]);
        let b = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Greater);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Smaller);

        assert!(a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_hm_gt_all() {
        let a = HashMap::from([("a", 2), ("b", 4), ("c", 6)]);
        let b = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Greater);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Smaller);

        assert!(a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_hm_gt_one_lt_one() {
        let a = HashMap::from([("a", 1), ("b", 3), ("c", 3)]);
        let b = HashMap::from([("a", 1), ("b", 2), ("c", 4)]);

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Incomparable);

        assert!(!a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(!b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_hm_different_keys() {
        let a = HashMap::from([("a", 1), ("x", 2), ("c", 3)]);
        let b = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);

        assert_eq!(a.part_cmp(&b), PartialOrdCompResult::Incomparable);
        assert_eq!(b.part_cmp(&a), PartialOrdCompResult::Incomparable);

        assert!(!a.is_greater_or_equal(&b));
        assert!(!b.is_greater_or_equal(&a));

        assert!(!a.is_smaller_or_equal(&b));
        assert!(!b.is_smaller_or_equal(&a));
    }

    #[test]
    fn test_display_partial_ord_comp_result() {
        let got_str = PartialOrdCompResult::Incomparable.to_string();
        assert_eq!(&got_str, "≠");

        let got_str = PartialOrdCompResult::Equal.to_string();
        assert_eq!(&got_str, "==");

        let got_str = PartialOrdCompResult::Greater.to_string();
        assert_eq!(&got_str, ">");

        let got_str = PartialOrdCompResult::Smaller.to_string();
        assert_eq!(&got_str, "<");
    }

    #[test]
    fn test_new_min_basis() {
        let config_1 = vec![1, 2, 3];
        let config_2 = vec![2, 2, 3];
        let config_3 = vec![4, 2, 1];
        let config_4 = vec![3, 2, 1];

        let min_basis_set = SetMinimalBasis::from(
            [
                config_1.clone(),
                config_2.clone(),
                config_3.clone(),
                config_4.clone(),
            ]
            .into_iter(),
        );

        let expected = SetMinimalBasis {
            configs: Vec::from([config_1.clone(), config_4.clone()]),
        };

        assert_eq!(min_basis_set, expected);

        let min_basis_set: Vec<_> = min_basis_set.into_iter().collect();
        let expected = Vec::from([config_1, config_4]);
        assert_eq!(min_basis_set, expected);

        let min_basis_set: Vec<_> = min_basis_set.to_vec();
        assert_eq!(min_basis_set, expected);
    }

    #[test]
    fn test_min_basis_retain() {
        let config_1 = vec![1, 2, 3];
        let config_2 = vec![1, 2];
        let config_3 = vec![5, 4];
        let config_4 = vec![3, 2, 1];

        let mut min_basis_set = SetMinimalBasis::from(
            [
                config_1.clone(),
                config_2.clone(),
                config_3.clone(),
                config_4.clone(),
            ]
            .into_iter(),
        );
        min_basis_set.retain(|cfg| cfg.len() == 3);

        let expected = SetMinimalBasis {
            configs: Vec::from([config_1, config_4]),
        };

        assert_eq!(min_basis_set, expected);
    }
}

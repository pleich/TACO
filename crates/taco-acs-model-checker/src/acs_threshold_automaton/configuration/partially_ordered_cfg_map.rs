//! A data structure for mapping [`ACSTAConfig`]s to a type `T` and
//! efficiently checking for comparable configurations.
//!
//! This module implements [`PartiallyOrderedConfigMap`] which maps from
//! [`ACSTAConfig`]s to some type `T` while allowing to easily find
//! [`ACSTAConfig`]s (and their keys) which are smaller with respect to the
//! defined [`PartialOrder`] than the given configuration.
//!
//! To enable the efficient lookup, the map builds a tree based on the
//! [`super::ACSIntervalState`] of the configuration. The data structure relies
//! on the fact that two intervals are only comparable if they are equal.
//!
//! Each variable in the [`super::ACSIntervalState`] (which are assumed to have
//! a stable order) corresponds to a layer of
//! `crate::error_graph::node::ErrorGraphNode`s
//! arranged in a vector (except the root node). The position in the vector
//! corresponds to the interval assignment of the variable (i.e. we can use
//! [`super::ACSInterval`] for efficient lookups). Each node then maintains a
//! map of location states to type `T`, that should be filled only in leafs of
//! the node.

use crate::{
    acs_threshold_automaton::configuration::{ACSLocState, ACSTAConfig},
    partial_ord::PartialOrder,
};

/// This struct maps from [`ACSTAConfig`]s to some type `T` while allowing to
/// easily find [`ACSTAConfig`]s (and their keys) which are smaller with respect
/// to the defined [`PartialOrder`] than the given configuration.
///
/// To enable the efficient lookup it uses a tree structure based on the
/// [`super::ACSIntervalState`] of the configuration
#[derive(Debug, PartialEq)]
pub struct PartiallyOrderedConfigMap<T: Clone> {
    /// Root node of the interval tree
    root: PartOrdMapNode<T>,
}

impl<T: Clone> Default for PartiallyOrderedConfigMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> PartiallyOrderedConfigMap<T> {
    /// Create a new empty [`PartiallyOrderedConfigMap`]
    pub fn new() -> Self {
        Self {
            root: PartOrdMapNode::new_empty(),
        }
    }

    /// Get the number of values in the map
    pub fn len(&self) -> usize {
        self.root.number_of_values()
    }

    /// Remove the entries with configuration `cfg`
    pub fn remove_entries_with_config(&mut self, cfg: &ACSTAConfig) {
        self.root.remove_entries_with_config(cfg, 0);
    }

    /// This function traverses the map and checks for configurations that are
    /// smaller or equal (which are returned in the first position of the tuple)
    /// and also checks for objects that are greater on in the well-quasi order
    /// (which are returned in the second position of the tuple).
    ///
    /// If multiple configurations smaller or equal exists one value to return
    /// is chosen non-deterministically.
    pub fn get_leq_or_bigger(&self, cfg: &ACSTAConfig) -> (Option<&T>, Option<&T>) {
        self.root.get_leq_or_bigger(cfg, 0)
    }

    /// Insert `value` with configuration `key` as key
    pub fn insert(&mut self, key: ACSTAConfig, value: T) {
        self.root.insert(key, value, 0);
    }

    /// Return all values stored in the map
    pub fn get_all_values(self) -> impl Iterator<Item = T> {
        self.root.get_all_values().into_iter()
    }

    /// Returns an iterator over the values stored in the map
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.root.values().into_iter()
    }
}

/// Internal type to represent the recursive structure of a
/// [`PartiallyOrderedConfigMap`]
#[derive(Debug, Clone, PartialEq)]
struct PartOrdMapNode<T: Clone> {
    /// This vector contains the actual entries of type `T` indexed by their
    /// location state
    ///
    /// This vector should usually only be filled if we are at the layer level
    /// equal to the number of variables in an [`super::ACSIntervalState`].
    /// This number should be consistent across all [`super::ACSIntervalState`]
    /// of configurations from the same threshold automaton.
    ///
    /// The data structure will however also work correctly with interval states
    /// of different length
    entries: Vec<(ACSLocState, T)>,
    /// Vector of children indexed by the interval the configuration had when
    /// they were inserted
    children: Vec<PartOrdMapNode<T>>,
}

impl<T: Clone> PartOrdMapNode<T> {
    /// Create a new empty node
    fn new_empty() -> Self {
        Self {
            entries: Vec::new(),
            children: Vec::new(),
        }
    }

    /// Count the number of values that are stored in the current tree
    fn number_of_values(&self) -> usize {
        self.children.iter().fold(self.entries.len(), |acc, child| {
            acc + child.number_of_values()
        })
    }

    /// Remove the entries with configuration `cfg`
    pub fn remove_entries_with_config(&mut self, cfg: &ACSTAConfig, level: usize) {
        if cfg.interval_state.v_to_interval.len() == level {
            self.entries.retain(|(e, _)| &cfg.loc_state != e);
            return;
        }

        debug_assert!(level < cfg.interval_state.v_to_interval.len());

        // Get the interval of the variable corresponding to the current level
        let interval = cfg.interval_state.v_to_interval[level].0;

        if let Some(child) = self.children.get_mut(interval) {
            child.remove_entries_with_config(cfg, level + 1);
        }
    }

    /// Search the map for a configuration that is smaller or equal (with
    /// respect to [`PartialOrder`]) than `cfg` and return its value
    ///
    /// If multiple configurations smaller or equal exists one value to return
    /// is chosen non-deterministically.
    fn get_leq_or_bigger(&self, cfg: &ACSTAConfig, level: usize) -> (Option<&T>, Option<&T>) {
        if cfg.interval_state.v_to_interval.len() == level {
            // We went through all variables and traversed all children according
            // to the interval assignment.
            // Therefore we know that the interval state of `cfg` is equal to
            // the state of the configuration the `entries` have been inserted
            // with.
            // Now we only need to check for smaller or equal location states
            return self.entries.iter().fold(
                (None, None),
                |(acc_leg, acc_gt), (existing_config, obj)| match existing_config
                    .part_cmp(cfg.location_state())
                {
                    crate::partial_ord::PartialOrdCompResult::Incomparable => (acc_leg, acc_gt),
                    crate::partial_ord::PartialOrdCompResult::Smaller
                    | crate::partial_ord::PartialOrdCompResult::Equal => (Some(obj), acc_gt),
                    crate::partial_ord::PartialOrdCompResult::Greater => (acc_leg, Some(obj)),
                },
            );
        }

        debug_assert!(level < cfg.interval_state.v_to_interval.len());

        // Get the interval of the variable corresponding to the current level
        let interval = cfg.interval_state.v_to_interval[level].0;

        // Get the child that had the same interval assignment
        if let Some(child) = self.children.get(interval) {
            return child.get_leq_or_bigger(cfg, level + 1);
        }

        (None, None)
    }

    /// Insert `value` with configuration `key` as key
    fn insert(&mut self, cfg: ACSTAConfig, value: T, level: usize) {
        if cfg.interval_state.v_to_interval.len() == level {
            debug_assert!(!self.entries.iter().any(|(e, _)| e == &cfg.loc_state));
            self.entries.push((cfg.loc_state, value));
            return;
        }

        debug_assert!(level < cfg.interval_state.v_to_interval.len());
        // Get the interval of the variable corresponding to the current level
        let interval = cfg.interval_state.v_to_interval[level].0;

        // Check if all children exists or insert them
        if self.children.len() <= interval {
            let elems_to_insert = interval - self.children.len() + 1;
            self.children
                .extend(vec![Self::new_empty(); elems_to_insert]);
        }

        // Insert child that had the same interval assignment
        self.children[interval].insert(cfg, value, level + 1);
    }

    /// Returns a vector of references over the values stored in the tree
    fn values(&self) -> Vec<&T> {
        self.entries
            .iter()
            .map(|(_, t)| t)
            .chain(self.children.iter().flat_map(|c| c.values()))
            .collect()
    }

    /// Return all values stored in the tree consuming self
    fn get_all_values(self) -> Vec<T> {
        self.entries
            .into_iter()
            .map(|(_, v)| v)
            .chain(self.children.into_iter().flat_map(|c| c.get_all_values()))
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, vec};

    use crate::acs_threshold_automaton::{
        ACSInterval,
        configuration::{
            ACSIntervalState, ACSLocState, ACSTAConfig,
            partially_ordered_cfg_map::{PartOrdMapNode, PartiallyOrderedConfigMap},
        },
    };

    #[test]
    fn test_partially_ordered_map_len() {
        let mut map = PartiallyOrderedConfigMap::default();

        assert_eq!(map.len(), 0);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(1)],
            },
        };

        map.insert(cfg.clone(), 42);

        assert_eq!(map.len(), 1);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 4],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 42);

        assert_eq!(map.len(), 2);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 5],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 43);

        assert_eq!(map.len(), 3);
    }

    #[test]
    fn test_partially_ordered_map_insert() {
        let mut map = PartiallyOrderedConfigMap::new();

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(1)],
            },
        };

        map.insert(cfg.clone(), 42);

        let expected_map = PartiallyOrderedConfigMap {
            root: PartOrdMapNode {
                entries: Vec::new(),
                children: vec![PartOrdMapNode {
                    entries: Vec::new(),
                    children: vec![
                        PartOrdMapNode {
                            entries: Vec::new(),
                            children: vec![],
                        },
                        PartOrdMapNode {
                            entries: vec![(cfg.loc_state.clone(), 42)],
                            children: vec![],
                        },
                    ],
                }],
            },
        };

        assert_eq!(map, expected_map);
    }

    #[test]
    fn test_partially_ordered_map_get_smaller_or_equal() {
        let mut map = PartiallyOrderedConfigMap::new();

        assert_eq!(map.len(), 0);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(1)],
            },
        };

        map.insert(cfg.clone(), 42);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 4],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 43);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 4],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };
        assert_eq!(map.get_leq_or_bigger(&cfg), (Some(&43), None));

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![10, 20, 500],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };
        assert_eq!(map.get_leq_or_bigger(&cfg), (Some(&43), None));

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![0, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };
        assert_eq!(map.get_leq_or_bigger(&cfg), (None, Some(&43)));

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(1), ACSInterval(0)],
            },
        };
        assert_eq!(map.get_leq_or_bigger(&cfg), (None, None));
    }

    #[test]
    fn test_partially_ordered_map_values() {
        let mut map = PartiallyOrderedConfigMap::new();

        assert_eq!(map.len(), 0);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(1)],
            },
        };

        map.insert(cfg.clone(), 42);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 4],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 43);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 6],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 44);

        assert_eq!(
            map.values().collect::<HashSet<_>>(),
            HashSet::from([&42, &43, &44])
        )
    }

    #[test]
    fn test_partially_ordered_map_get_all_values() {
        let mut map = PartiallyOrderedConfigMap::new();

        assert_eq!(map.len(), 0);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 3],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(1)],
            },
        };

        map.insert(cfg.clone(), 42);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 4],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 43);

        let cfg = ACSTAConfig {
            loc_state: ACSLocState {
                loc_state: vec![1, 2, 6],
            },
            interval_state: ACSIntervalState {
                v_to_interval: vec![ACSInterval(0), ACSInterval(0)],
            },
        };

        map.insert(cfg.clone(), 44);

        assert_eq!(
            map.get_all_values().collect::<HashSet<_>>(),
            HashSet::from([42, 43, 44])
        )
    }
}

//! This module implements the BDD trait for the
//! [OxiDD](https://github.com/OxiDD/oxidd) library
//!
//! TODO: With the release of oxidd v0.0.11 the API has changed significantly,
//! for now everything has only been fixed to "work", but there is a lot of room
//! for improvement.

use oxidd::{
    BooleanFunction, BooleanFunctionQuant, FunctionSubst, Manager, ManagerRef, Subst,
    bdd::{BDDFunction, BDDManagerRef},
};
use std::{fmt::Debug, rc::Rc, sync::Mutex};

use super::{Bdd, BddManager};

#[cfg(feature = "config_deserialize")]
use serde::Deserialize;

/// Maximum number of nodes in the BDD manager
/// Exceeding this limit will cause the manager to panic
const INNER_NODE_CAPACITY: usize = 1 << 20;
/// Maximum number of nodes in the apply cache
const APPLY_CACHE_CAPACITY: usize = 1024;
/// Number of threads used for parallel operations
const THREADS: u32 = 8;

/// BDD type for OxiDD BDDs
#[derive(Clone)]
pub struct OxiDD {
    /// BDD representation of the variable
    bdd: oxidd::bdd::BDDFunction,
    /// If the BDD is a variable, contains the variable id
    var_id: Option<u32>,
}

impl Debug for OxiDD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "OxiDD does not support prints")
    }
}

impl Bdd for OxiDD {
    fn not(&self) -> Self {
        OxiDD {
            bdd: self
                .bdd
                .not()
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity"),
            var_id: None,
        }
    }

    fn and(&self, rhs: &Self) -> Self {
        OxiDD {
            bdd: self
                .bdd
                .and(&rhs.bdd)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity"),
            var_id: None,
        }
    }

    fn or(&self, rhs: &Self) -> Self {
        OxiDD {
            bdd: self
                .bdd
                .or(&rhs.bdd)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity"),
            var_id: None,
        }
    }

    fn exists<'a, I: IntoIterator<Item = &'a Self>>(&'a self, vars: I) -> Self {
        let mut vars = vars.into_iter().map(|dd| dd.bdd.clone());

        let first = vars.next();
        if first.is_none() {
            panic!("No variable for existential quantification");
        }
        let first =
            first.expect("OxiDD ran out of memory. Consider trying again with increased capacity");

        let vars = vars.fold(first, |acc, x| {
            acc.and(&x)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity")
        });

        OxiDD {
            bdd: self
                .bdd
                .exists(&vars)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity"),
            var_id: None,
        }
    }

    fn satisfiable(&self) -> bool {
        self.bdd.satisfiable()
    }

    fn implies(&self, rhs: &Self) -> Self {
        OxiDD {
            bdd: self
                .bdd
                .imp(&rhs.bdd)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity"),
            var_id: None,
        }
    }

    fn equiv(&self, rhs: &Self) -> Self {
        OxiDD {
            bdd: self
                .bdd
                .equiv(&rhs.bdd)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity"),
            var_id: None,
        }
    }

    fn swap<'a, I: IntoIterator<Item = &'a Self>>(&'a self, from: I, to: I) -> Self {
        let mut vars = Vec::new();
        let mut replacements = Vec::new();

        from.into_iter().zip(to).for_each(|(from, to)| {
            let var_id_from = from.var_id.expect("Substitution not on variable");

            vars.push(var_id_from);
            replacements.push(to.bdd.clone());

            let var_id_to = to.var_id.expect("Substitution not on variable");
            vars.push(var_id_to);
            replacements.push(from.bdd.clone());
        });

        let subs = Subst::new(vars, replacements);
        let bdd = self
            .bdd
            .substitute(&subs)
            .expect("OxiDD ran out of memory. Consider trying again with increased capacity");

        OxiDD { bdd, var_id: None }
    }
}

impl PartialEq for OxiDD {
    // We consider two bdds `a` and `b` are equal  if they are equivalent, i.e.,
    // iff: (a <=> b).is_sat() & !(a <=> b).is_unsat()
    fn eq(&self, other: &Self) -> bool {
        let equiv = self.equiv(other);
        let equiv_sat = equiv.satisfiable();
        let n_equiv_unsat = !equiv.not().satisfiable();
        equiv_sat && n_equiv_unsat
    }
}

/// Configuration for the OxiDD BDD manager
///
/// See <https://docs.rs/oxidd/latest/oxidd/bdd/fn.new_manager.html>
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub struct OxiddManagerConfig {
    #[cfg_attr(
        feature = "config_deserialize",
        serde(default = "default_inner_node_capacity")
    )]
    pub inner_node_capacity: usize,
    #[cfg_attr(
        feature = "config_deserialize",
        serde(default = "default_apply_cache_capacity")
    )]
    pub apply_cache_capacity: usize,
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_threads"))]
    pub threads: u32,
}

/// Function to get default inner node capacity for the BDD manager
fn default_inner_node_capacity() -> usize {
    INNER_NODE_CAPACITY
}

/// Function to get default apply cache capacity for the BDD manager
fn default_apply_cache_capacity() -> usize {
    APPLY_CACHE_CAPACITY
}

/// Function to get default number of threads for the BDD manager
fn default_threads() -> u32 {
    THREADS
}

impl Default for OxiddManagerConfig {
    fn default() -> Self {
        Self {
            inner_node_capacity: default_inner_node_capacity(),
            apply_cache_capacity: default_apply_cache_capacity(),
            threads: default_threads(),
        }
    }
}

/// BDD manager for OxiDD BDDs
///
/// This manager is a wrapper around the OxiDD BDD manager. It panics if the BDD
/// manager runs out of memory.
///
/// By default the manager is configured to have a maximum of 2^30 nodes and 2^10
/// nodes in the apply cache.
#[derive(Clone)]
pub struct OxiddManager {
    /// Reference to the manager
    mgr: BDDManagerRef,
    /// Index of the next variable to be created
    next_var_index: Rc<Mutex<u32>>,
}

impl PartialEq for OxiddManager {
    /// Compare based on the manager objects
    fn eq(&self, other: &Self) -> bool {
        self.mgr == other.mgr
    }
}

impl OxiddManager {
    /// Create a new Oxidd BDD manager with default configuration
    ///
    /// This manager internally uses the
    /// [OxiDD BDD library](https://github.com/OxiDD/oxidd/tree/main)
    /// to create and manipulate BDDs.
    ///
    /// This manager panics if it runs out of memory. By default the manager is
    /// configured to have a maximum of 2^30 nodes and 2^10 nodes in the apply
    /// cache.
    pub fn new() -> Self {
        Self {
            mgr: oxidd::bdd::new_manager(INNER_NODE_CAPACITY, APPLY_CACHE_CAPACITY, THREADS),
            next_var_index: Rc::new(Mutex::new(0)),
        }
    }

    /// Create a new Oxidd BDD manager with custom configuration
    pub fn new_with_config(config: &OxiddManagerConfig) -> Self {
        Self {
            mgr: oxidd::bdd::new_manager(
                config.inner_node_capacity,
                config.apply_cache_capacity,
                config.threads,
            ),
            next_var_index: Rc::new(Mutex::new(0)),
        }
    }
}

impl Default for OxiddManager {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for OxiddManager {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        oxidd::bdd::print_stats();
        Ok(())
    }
}

impl BddManager for OxiddManager {
    type DD = OxiDD;

    fn new_var(&mut self) -> Self::DD {
        let mut index = self.next_var_index.lock().unwrap();
        let new_var_index = *index;
        *index += 1;

        let inner = self.mgr.with_manager_exclusive(|mgr| {
            mgr.add_named_vars([new_var_index.to_string()])
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity");

            BDDFunction::var(mgr, new_var_index)
                .expect("OxiDD ran out of memory. Consider trying again with increased capacity")
        });
        OxiDD {
            bdd: inner,
            var_id: Some(new_var_index),
        }
    }

    fn get_bdd_false(&self) -> Self::DD {
        let inner = self.mgr.with_manager_exclusive(|mgr| BDDFunction::f(mgr));
        OxiDD {
            bdd: inner,
            var_id: None,
        }
    }

    fn get_bdd_true(&self) -> Self::DD {
        let inner = self.mgr.with_manager_exclusive(|mgr| BDDFunction::t(mgr));
        OxiDD {
            bdd: inner,
            var_id: None,
        }
    }

    #[cfg(feature = "visualize")]
    fn dump_dot<'a, VN, BD>(
        &'a self,
        file: std::fs::File,
        _bdds: impl IntoIterator<Item = (&'a Self::DD, BD)>,
        var_name: impl IntoIterator<Item = (&'a Self::DD, VN)>,
    ) -> std::io::Result<()>
    where
        VN: std::fmt::Display + Clone,
        BD: std::fmt::Display,
    {
        self.mgr.with_manager_shared(|manager| {
            let var_name = var_name.into_iter().map(|(dd, vn)| (&dd.bdd, vn));

            oxidd_dump::dot::dump_all(file, manager, var_name)
        })
    }
}

#[cfg(test)]
mod test {
    use crate::{
        BddManager,
        bdd_test_utils::{self, test_mgr_eq_and_clone},
    };

    use super::OxiddManager;

    #[test]
    fn test_mgr_eq() {
        let mgr1 = OxiddManager::default();
        let mgr2 = OxiddManager::default();

        test_mgr_eq_and_clone(mgr1, mgr2);
    }

    #[test]
    fn test_mgr_get() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_mgr_get(mgr)
    }

    #[test]
    fn test_not() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_not(mgr)
    }

    #[test]
    fn test_and() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_and(mgr)
    }

    #[test]
    fn test_or() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_or(mgr)
    }

    #[test]
    fn test_exists() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_exists(mgr)
    }

    #[test]
    fn test_implies() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_implies(mgr)
    }

    #[test]
    fn test_equiv() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_equiv(mgr)
    }

    #[test]
    fn test_swap() {
        let mgr = OxiddManager::default();
        bdd_test_utils::test_swap(mgr)
    }

    #[test]
    #[should_panic]
    fn test_panic_on_bdd_of_mixed_mgrs() {
        let mgr1 = OxiddManager::default();
        let mgr2 = OxiddManager::default();
        bdd_test_utils::panic_on_bdd_of_mixed_mgrs(mgr1, mgr2)
    }

    #[test]
    fn print_funcs_work() {
        let mut mgr = OxiddManager::new();
        let v = mgr.new_var();

        println!("Debug: {v:?}");
        println!("Mgr Debug: {mgr:?}");
    }
}

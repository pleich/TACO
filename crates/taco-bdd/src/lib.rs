//! Common interface for binary decision diagrams (BDDs) and BDD managers
//!
//! This package provides a generic interface for BDDs and BDD managers,
//! allowing the use of multiple BDD libraries, depending on your needs.
//! Currently, this package includes CUDD and OxiDD:
//! - [CUDD](https://github.com/cuddorg/cudd)
//! - [OxiDD](https://github.com/OxiDD/oxidd)
//!
//! To interface with BDDs use the [`BDD`] and [`BDDManager`] types, as well as
//! the [`BDDManagerConfig`] to configure the different managers.
//!
//! To add a new BDD library, implement the [`Bdd`]  and [`BddManager`] traits
//! for the library, add it as new module and add a variant for the new library
//! to the [`BDD`] and [`BDDManager`] types.

use std::{fmt::Debug, ops};

#[cfg(feature = "cudd")]
use cudd::{CuddDD, CuddManager};
#[cfg(feature = "oxidd")]
use oxidd::{OxiDD, OxiddManager};
#[cfg(feature = "config_deserialize")]
use serde::Deserialize;

/// CUDD library
#[cfg(feature = "cudd")]
#[allow(unsafe_code)]
mod cudd;

/// OxiDD library
#[cfg(feature = "oxidd")]
mod oxidd;

/// Common representation of a binary decision diagram (BDD)
///
/// This enum defines a variant for each library that can be used. Note that
/// combining BDDs of different libraries and managers will generally result in
/// panics.
///
/// Currently, the supported BDD libraries are:
/// - [CUDD](https://github.com/ivmai/cudd)
/// - [OxiDD](https://github.com/OxiDD/oxidd)
#[derive(Debug, Clone, PartialEq)]
pub enum BDD {
    /// A CUDD BDD
    #[cfg(feature = "cudd")]
    CuDD(CuddDD),
    /// An OxiDD BDD
    #[cfg(feature = "oxidd")]
    OxiDD(OxiDD),
}

impl Bdd for BDD {
    fn not(&self) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => BDD::CuDD(dd.not()),
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => BDD::OxiDD(dd.not()),
        }
    }

    #[allow(unreachable_patterns)]
    fn and(&self, rhs: &Self) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => match rhs {
                BDD::CuDD(rhs_dd) => BDD::CuDD(dd.and(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => match rhs {
                BDD::OxiDD(rhs_dd) => BDD::OxiDD(dd.and(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
        }
    }

    #[allow(unreachable_patterns)]
    fn or(&self, rhs: &Self) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => match rhs {
                BDD::CuDD(rhs_dd) => BDD::CuDD(dd.or(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => match rhs {
                BDD::OxiDD(rhs_dd) => BDD::OxiDD(dd.or(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
        }
    }

    #[allow(unreachable_patterns)]
    fn exists<'a, I: IntoIterator<Item = &'a Self>>(&'a self, vars: I) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => BDD::CuDD(dd.exists(vars.into_iter().map(|v| match v {
                BDD::CuDD(v) => v,
                _ => panic!("BDDs are from different managers"),
            }))),
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => BDD::OxiDD(dd.exists(vars.into_iter().map(|v| match v {
                BDD::OxiDD(v) => v,
                _ => panic!("BDDs are from different managers"),
            }))),
        }
    }

    fn satisfiable(&self) -> bool {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => dd.satisfiable(),
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => dd.satisfiable(),
        }
    }

    #[allow(unreachable_patterns)]
    fn implies(&self, rhs: &Self) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => match rhs {
                BDD::CuDD(rhs_dd) => BDD::CuDD(dd.implies(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => match rhs {
                BDD::OxiDD(rhs_dd) => BDD::OxiDD(dd.implies(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
        }
    }

    #[allow(unreachable_patterns)]
    fn equiv(&self, rhs: &Self) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => match rhs {
                BDD::CuDD(rhs_dd) => BDD::CuDD(dd.equiv(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => match rhs {
                BDD::OxiDD(rhs_dd) => BDD::OxiDD(dd.equiv(rhs_dd)),
                _ => panic!("BDDs are from different managers"),
            },
        }
    }

    #[allow(unreachable_patterns)]
    fn swap<'a, I: IntoIterator<Item = &'a Self>>(&'a self, from: I, to: I) -> Self {
        match self {
            #[cfg(feature = "cudd")]
            BDD::CuDD(dd) => {
                let to_cudd = |v: &'a BDD| match v {
                    BDD::CuDD(v) => v,
                    _ => panic!("BDDs are from different managers"),
                };

                let to = to.into_iter().map(to_cudd);
                let from = from.into_iter().map(to_cudd);

                BDD::CuDD(dd.swap(from, to))
            }
            #[cfg(feature = "oxidd")]
            BDD::OxiDD(dd) => {
                let to_oxidd = |v: &'a BDD| match v {
                    BDD::OxiDD(v) => v,
                    _ => panic!("BDDs are from different managers"),
                };

                let to = to.into_iter().map(to_oxidd);
                let from = from.into_iter().map(to_oxidd);

                BDD::OxiDD(dd.swap(from, to))
            }
        }
    }
}

impl ops::Not for &BDD {
    type Output = BDD;

    fn not(self) -> BDD {
        Bdd::not(self)
    }
}

impl ops::Not for BDD {
    type Output = BDD;

    fn not(self) -> BDD {
        Bdd::not(&self)
    }
}

impl ops::BitAnd for &BDD {
    type Output = BDD;

    fn bitand(self, rhs: Self) -> BDD {
        Bdd::and(self, rhs)
    }
}

impl ops::BitAnd for BDD {
    type Output = BDD;

    fn bitand(self, rhs: Self) -> BDD {
        Bdd::and(&self, &rhs)
    }
}

impl ops::BitAndAssign for BDD {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = Bdd::and(self, &rhs);
    }
}

impl ops::BitOr for &BDD {
    type Output = BDD;

    fn bitor(self, rhs: Self) -> BDD {
        Bdd::or(self, rhs)
    }
}

impl ops::BitOr for BDD {
    type Output = BDD;

    fn bitor(self, rhs: Self) -> BDD {
        Bdd::or(&self, &rhs)
    }
}

impl ops::BitOrAssign for BDD {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = Bdd::or(self, &rhs);
    }
}

/// Configuration for a BDD manager
///
/// This struct is the common interface for configuration of a BDD manager.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub enum BDDManagerConfig {
    /// CUDD manager configuration
    #[cfg(feature = "cudd")]
    Cudd(cudd::CuddManagerConfig),
    /// OxiDD manager configuration
    #[cfg(feature = "oxidd")]
    Oxidd(oxidd::OxiddManagerConfig),
}

impl BDDManagerConfig {
    /// Create a new BDD manager with the current configuration
    pub fn mgr_from_config(&self) -> BDDManager {
        match self {
            #[cfg(feature = "cudd")]
            BDDManagerConfig::Cudd(cfg) => BDDManager::new_cudd_with_config(cfg),
            #[cfg(feature = "oxidd")]
            BDDManagerConfig::Oxidd(cfg) => BDDManager::new_oxidd_with_config(cfg),
        }
    }

    /// Get the default configuration for the cudd BDD manager
    #[cfg(feature = "cudd")]
    pub fn new_cudd() -> Self {
        BDDManagerConfig::Cudd(cudd::CuddManagerConfig::default())
    }

    /// Get the default configuration for the oxidd BDD manager
    #[cfg(feature = "oxidd")]
    pub fn new_oxidd() -> Self {
        BDDManagerConfig::Oxidd(oxidd::OxiddManagerConfig::default())
    }
}

/// The `BDDManager` type allows to interface with BDD Managers from different
/// libraries.
///
/// Currently, the supported BDD libraries are:
/// - [CUDD](https://github.com/ivmai/cudd)
/// - [OxiDD](https://github.com/OxiDD/oxidd)
#[derive(Debug, Clone, PartialEq)]
pub enum BDDManager {
    /// CUDD BDD library backend
    #[cfg(feature = "cudd")]
    CuDD(CuddManager),
    /// OxiDD BDD library backend
    #[cfg(feature = "oxidd")]
    OxiDD(OxiddManager),
}

impl BDDManager {
    /// Create a new BDD manager with the given configuration
    pub fn new(cfg: &BDDManagerConfig) -> Self {
        cfg.mgr_from_config()
    }

    /// Create a new Oxidd BDD manager with default configuration.
    #[cfg(feature = "oxidd")]
    pub fn new_oxidd() -> Self {
        BDDManager::OxiDD(OxiddManager::default())
    }

    /// Create a new Oxidd BDD manager with custom configuration.
    #[cfg(feature = "oxidd")]
    pub fn new_oxidd_with_config(cfg: &oxidd::OxiddManagerConfig) -> Self {
        BDDManager::OxiDD(OxiddManager::new_with_config(cfg))
    }

    /// Create a new CUDD BDD manager with default configuration.
    #[cfg(feature = "cudd")]
    pub fn new_cudd() -> Self {
        BDDManager::CuDD(CuddManager::default())
    }

    /// Create a new CUDD BDD manager with custom configuration.
    #[cfg(feature = "cudd")]
    pub fn new_cudd_with_config(cfg: &cudd::CuddManagerConfig) -> Self {
        BDDManager::CuDD(CuddManager::new_with_config(cfg))
    }
}

impl Default for BDDManager {
    /// Default BDD manager is the CUDD manager, if the `cudd` feature is
    /// enabled. Otherwise, it will default to the OxiDD manager or panic if no
    /// BDD library is enabled during compilation.
    #[allow(unreachable_code)]
    fn default() -> Self {
        #[cfg(feature = "cudd")]
        return BDDManager::CuDD(CuddManager::default());
        #[cfg(feature = "oxidd")]
        return BDDManager::OxiDD(OxiddManager::default());
        panic!("No BDD library enabled during compilation");
    }
}

impl BddManager for BDDManager {
    type DD = BDD;

    fn new_var(&mut self) -> Self::DD {
        match self {
            #[cfg(feature = "cudd")]
            BDDManager::CuDD(mgr) => BDD::CuDD(mgr.new_var()),
            #[cfg(feature = "oxidd")]
            BDDManager::OxiDD(mgr) => BDD::OxiDD(mgr.new_var()),
        }
    }

    fn get_bdd_false(&self) -> Self::DD {
        match self {
            #[cfg(feature = "cudd")]
            BDDManager::CuDD(mgr) => BDD::CuDD(mgr.get_bdd_false()),
            #[cfg(feature = "oxidd")]
            BDDManager::OxiDD(mgr) => BDD::OxiDD(mgr.get_bdd_false()),
        }
    }

    fn get_bdd_true(&self) -> Self::DD {
        match self {
            #[cfg(feature = "cudd")]
            BDDManager::CuDD(mgr) => BDD::CuDD(mgr.get_bdd_true()),
            #[cfg(feature = "oxidd")]
            BDDManager::OxiDD(mgr) => BDD::OxiDD(mgr.get_bdd_true()),
        }
    }

    #[cfg(feature = "visualize")]
    fn dump_dot<'a, VN, BN>(
        &'a self,
        file: std::fs::File,
        bdd_names: impl IntoIterator<Item = (&'a Self::DD, BN)>,
        variable_names: impl IntoIterator<Item = (&'a Self::DD, VN)>,
    ) -> std::io::Result<()>
    where
        VN: std::fmt::Display + Clone,
        BN: std::fmt::Display,
    {
        match self {
            #[cfg(feature = "cudd")]
            BDDManager::CuDD(mgr) => mgr.dump_dot(
                file,
                bdd_names.into_iter().map(|(bdd, name)| match bdd {
                    BDD::CuDD(dd) => (dd, name),
                    _ => panic!("BDDs are from different managers"),
                }),
                variable_names.into_iter().map(|(bdd, name)| match bdd {
                    BDD::CuDD(dd) => (dd, name),
                    _ => panic!("BDDs are from different managers"),
                }),
            ),
            #[cfg(feature = "oxidd")]
            BDDManager::OxiDD(mgr) => mgr.dump_dot(
                file,
                bdd_names.into_iter().map(|(bdd, name)| match bdd {
                    BDD::OxiDD(dd) => (dd, name),
                    _ => panic!("BDDs are from different managers"),
                }),
                variable_names.into_iter().map(|(bdd, name)| match bdd {
                    BDD::OxiDD(dd) => (dd, name),
                    _ => panic!("BDDs are from different managers"),
                }),
            ),
        }
    }
}

/// The `BDD` trait defines the interface for a binary decision diagram.
pub trait Bdd: Sized + Debug + PartialEq + Clone {
    /// Negation of a BDD.
    fn not(&self) -> Self;

    /// Conjunction of two BDDs.
    fn and(&self, rhs: &Self) -> Self;

    /// Disjunction of two BDDs.
    fn or(&self, rhs: &Self) -> Self;

    /// Existential quantification over a set of variables `vars`
    fn exists<'a, I: IntoIterator<Item = &'a Self>>(&'a self, vars: I) -> Self;

    /// Check whether a satisfying assignment exists for the BDD.
    fn satisfiable(&self) -> bool;

    /// Compute the implication of two BDDs, i.e., the bdd `lhs => rhs`.
    fn implies(&self, rhs: &Self) -> Self;

    /// Compute the equivalence of two BDDs, i.e., the bdd `lhs <=> rhs`.
    fn equiv(&self, rhs: &Self) -> Self;

    /// Swap variables according to the permutation.
    fn swap<'a, I: IntoIterator<Item = &'a Self>>(&'a self, from: I, to: I) -> Self;
}

/// The `BDDManager` trait defines the interface for a BDD manager. The
/// associated  type `DD` is the type of BDDs created by this manager.
pub trait BddManager: Debug + PartialEq + Clone + Default {
    /// The type of BDDs created by the manager.
    type DD: Bdd;

    /// Create a new BDD that is not referenced yet.
    fn new_var(&mut self) -> Self::DD;

    /// Get false BDD
    fn get_bdd_false(&self) -> Self::DD;

    /// Get true BDD
    fn get_bdd_true(&self) -> Self::DD;

    #[cfg(feature = "visualize")]
    /// Write a file in the `dot` format visualizing all BDDs included in
    /// `bdd_names`
    ///
    /// This function will create a file in the `dot` format that visualizes all
    /// BDDs in `bdd_names`, and associating them with the names given by the
    /// second argument of the tuple in the iterator.
    ///
    /// Optionally, variables can be named in the visualization by supplying
    /// the variable names in the `variable_names` iterator.
    /// Note that, when working with CUDD the variable names must be supplied in
    /// as an iterator according to the index of the variable.
    ///
    ///
    /// # Example
    ///
    /// ```ignore
    /// use bdd::{BDDManager, Bdd, BddManager};
    ///
    /// let var1 = mgr.new_var();
    /// let var2 = mgr.new_var();
    /// let var3 = mgr.new_var();
    ///
    /// let node = var1.and(&var2);
    /// let node = node.or(&var3);
    ///
    /// let file = std::fs::File::create("./test-doc.dot").unwrap();
    /// mgr.dump_dot(
    ///        file,
    ///        vec![(&node, "foo")],
    ///        vec![(&var1, "var1"), (&var2, "var2"), (&var3, "var3")],
    ///    ).unwrap();
    ///
    /// std::fs::remove_file(file).unwrap();
    /// ```
    fn dump_dot<'a, VN, BN>(
        &'a self,
        file: std::fs::File,
        bdd_names: impl IntoIterator<Item = (&'a Self::DD, BN)>,
        variable_names: impl IntoIterator<Item = (&'a Self::DD, VN)>,
    ) -> std::io::Result<()>
    where
        VN: std::fmt::Display + Clone,
        BN: std::fmt::Display;
}

/// Trait for types that can provide a preconfigured BDDManager
///
/// This trait is implemented by types that can provide configured BDDManagers.
/// For example, this trait can be implemented by model checker contexts.
pub trait ProvidesBDDManager {
    /// Get a new, already configured bdd manager
    fn get_new_bdd_manager(&self) -> BDDManager;
}

impl ProvidesBDDManager for BDDManager {
    fn get_new_bdd_manager(&self) -> BDDManager {
        self.clone()
    }
}

/// This module defines generic tests for BDD managers and BDDs. These tests can
/// be used as a sanity check for libraries, but are not exhaustive.
#[cfg(test)]
mod bdd_test_utils {

    use crate::Bdd;

    use super::BddManager;

    /// Tests equality between two BDD managers and their clones.
    pub(crate) fn test_mgr_eq_and_clone<T: BddManager>(mgr1: T, mgr2: T) {
        assert_ne!(mgr1, mgr2);
        assert_eq!(mgr1, mgr1.clone());
    }

    pub(crate) fn test_mgr_get<T: BddManager>(mut mgr: T) {
        let f = mgr.get_bdd_false();
        assert!(!f.satisfiable());

        let t = mgr.get_bdd_true();
        assert!(t.satisfiable());

        let var = mgr.new_var();
        assert!(var.satisfiable())
    }

    pub(crate) fn test_not<T: BddManager>(mut mgr: T) {
        let f = mgr.get_bdd_false();
        assert!(f.not().satisfiable());

        let t = mgr.get_bdd_true();
        assert!(!t.not().satisfiable());

        let var = mgr.new_var();
        assert!(var.not().satisfiable());
    }

    pub(crate) fn test_and<T: BddManager>(mut mgr: T) {
        let f = mgr.get_bdd_false();
        let t = mgr.get_bdd_true();

        assert!(t.and(&t).satisfiable());
        assert!(!t.and(&f).satisfiable());
        assert!(!f.and(&t).satisfiable());
        assert!(!f.and(&f).satisfiable());

        let var = mgr.new_var();
        assert!(t.and(&var).satisfiable());
        assert!(var.and(&t).satisfiable());

        assert!(!f.and(&var).satisfiable());
        assert!(!var.and(&f).satisfiable());
    }

    pub(crate) fn test_or<T: BddManager>(mut mgr: T) {
        let f = mgr.get_bdd_false();
        let t = mgr.get_bdd_true();

        assert!(t.or(&t).satisfiable());
        assert!(t.or(&f).satisfiable());
        assert!(f.or(&t).satisfiable());
        assert!(!f.or(&f).satisfiable());

        let var = mgr.new_var();
        assert!(t.or(&var).satisfiable());
        assert!(var.or(&t).satisfiable());

        assert!(f.or(&var).satisfiable());
        assert!(var.or(&f).satisfiable());
    }

    pub(crate) fn test_exists<T: BddManager>(mut mgr: T) {
        let var0 = mgr.new_var();
        let var1 = mgr.new_var();
        let var2 = mgr.new_var();
        let var3 = mgr.new_var();

        let con = var0.and(&var1).and(&var3);
        assert_eq!(con.exists(vec![&var0, &var1, &var2]), var3)
    }

    pub(crate) fn test_implies<T: BddManager>(mut mgr: T) {
        let var1 = mgr.new_var();

        let con1 = &var1;
        let con2 = &var1.not();

        assert_eq!(con1.implies(con2).and(&var1), mgr.get_bdd_false());

        assert_eq!(con1.implies(&con2.not()), mgr.get_bdd_true());
    }

    pub(crate) fn test_equiv<T: BddManager>(mut mgr: T) {
        let var0 = mgr.new_var();
        let var1 = mgr.new_var();
        let var2 = mgr.new_var();
        let var3 = mgr.new_var();

        let con1 = var0.and(&var1).and(&var2);
        let con2 = var0.and(&var3).and(&var2);

        assert!(con1.equiv(&con2).satisfiable());

        let con3 = var0.and(&var1).and(&var2);
        let con4 = var0.and(&var1).and(&var2);

        assert_eq!(con3.equiv(&con4), mgr.get_bdd_true());

        let con5 = &var1;
        let con6 = &var1.not();
        assert_eq!(con5.equiv(con6), mgr.get_bdd_false());
    }

    pub(crate) fn test_swap<T: BddManager>(mut mgr: T) {
        let var0 = mgr.new_var();
        let var1 = mgr.new_var();
        let var2 = mgr.new_var();
        let var3 = mgr.new_var();

        let con1 = var0.and(&var1).and(&var2);
        let expected_con = var0.and(&var3).and(&var2);

        assert_eq!(con1.swap(vec![&var1], vec![&var3]), expected_con);
    }

    pub(crate) fn test_swap_behavior_primed_var_in_bdd<T: BddManager>(mut mgr: T) {
        let l_0 = mgr.new_var();
        let l_0_prime = mgr.new_var();

        // this should be bitwise
        let r_0 = mgr.new_var();

        let test_bdd = l_0.and(&r_0.and(&l_0_prime.not()));
        let test_bdd = test_bdd.swap(&vec![l_0.clone()], &vec![l_0_prime.clone()]);

        let unexpected_bdd = l_0_prime.and(&r_0.and(&l_0_prime.not()));
        assert_ne!(test_bdd, unexpected_bdd);

        let expected_bdd = l_0_prime.and(&r_0.and(&l_0.not()));
        assert_eq!(test_bdd, expected_bdd)
    }

    /// Expected behavior: panic when trying to create a BDD with different
    /// managers.
    pub(crate) fn panic_on_bdd_of_mixed_mgrs<T: BddManager>(mut mgr1: T, mut mgr2: T) {
        let bdd1 = mgr1.new_var();
        let bdd2 = mgr2.new_var();

        bdd1.and(&bdd2);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use bdd_test_utils::*;

    fn test_all_functions(f: impl Fn() -> BDDManager) {
        let mgr1 = f();
        let mgr2 = f();

        test_mgr_eq_and_clone(mgr1, mgr2);

        let mgr = f();
        test_mgr_get::<BDDManager>(mgr);

        let mgr = f();
        test_not(mgr);

        let mgr = f();
        test_and(mgr);

        let mgr = f();
        test_or(mgr);

        let mgr = f();
        test_exists(mgr);

        let mgr = f();
        test_implies(mgr);

        let mgr = f();
        test_equiv(mgr);

        let mgr = f();
        test_swap(mgr);

        let mgr = f();
        test_swap_behavior_primed_var_in_bdd(mgr);
    }

    fn test_operators(f: impl Fn() -> BDDManager) {
        let mut mgr = f();

        // Test operator implementation on BDD
        let bdd1 = mgr.new_var();
        let bdd2 = mgr.new_var();

        // Test NOT operator
        assert_eq!(!&bdd1, bdd1.not());

        // Test AND operator
        assert_eq!(&bdd1 & &bdd2, bdd1.and(&bdd2));
        assert_eq!(bdd1.clone() & bdd2.clone(), bdd1.and(&bdd2));
        let mut bdd3 = bdd1.clone();
        bdd3 &= bdd2.clone();
        assert_eq!(bdd3, bdd1.and(&bdd2));

        // Test OR operator
        assert_eq!(&bdd1 | &bdd2, bdd1.or(&bdd2));
        assert_eq!(bdd1.clone() | bdd2.clone(), bdd1.or(&bdd2));
        let mut bdd3 = bdd1.clone();
        bdd3 |= bdd2.clone();
        assert_eq!(bdd3, bdd1.or(&bdd2));
    }

    #[cfg(feature = "cudd")]
    #[test]
    fn test_cudd_functional() {
        test_all_functions(BDDManager::new_cudd);
        test_all_functions(|| BDDManagerConfig::new_cudd().mgr_from_config());
        test_all_functions(|| BDDManager::new(&BDDManagerConfig::new_cudd()));
        test_all_functions(BDDManager::default);
        test_operators(BDDManager::new_cudd);
    }

    #[cfg(feature = "oxidd")]
    #[test]
    fn test_oxidd_functional() {
        test_all_functions(BDDManager::new_oxidd);
        test_all_functions(|| BDDManagerConfig::new_oxidd().mgr_from_config());
        test_all_functions(|| BDDManager::new(&BDDManagerConfig::new_oxidd()));
        test_all_functions(BDDManager::default);
        test_operators(BDDManager::new_oxidd);
    }

    #[test]
    #[cfg(all(feature = "oxidd", feature = "cudd"))]
    #[should_panic]
    fn test_panic_on_bdd_of_mixed_mgrs() {
        let mgr1 = BDDManager::new_cudd();
        let mgr2 = BDDManager::new_oxidd();
        panic_on_bdd_of_mixed_mgrs(mgr1, mgr2);
    }
}

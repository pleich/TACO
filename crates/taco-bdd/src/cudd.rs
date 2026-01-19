//! BDD interface implementation for [CUDD](https://github.com/ivmai/cudd)
//!
//! The bindings to the C library, as well as the build mechanisms are provided
//! by the `cudd-sys` crate.
//!
//! The [`CuddManager`] struct is the manager for the CUDD BDDs and implements
//! the [`BDDManager`] trait. The [`CuddDD`] struct is the BDD type for CUDD
//! BDDs and implements the [`BDD`] trait.
//!
//! Note that this module uses unsafe code to interact with the CUDD library.

#[cfg(feature = "visualize")]
use std::{ffi::CString, os::fd::AsRawFd};

#[cfg(feature = "config_deserialize")]
use serde::Deserialize;

use std::{
    fmt::{Debug, Display},
    ptr::null,
    rc::Rc,
    sync::Mutex,
};

use cudd_sys::cudd::{
    Cudd_CountPathsToNonZero, Cudd_Init, Cudd_Not, Cudd_PrintDebug, Cudd_PrintInfo,
    Cudd_PrintMinterm, Cudd_Quit, Cudd_ReadLogicZero, Cudd_ReadOne, Cudd_RecursiveDeref, Cudd_Ref,
    Cudd_bddAnd, Cudd_bddComputeCube, Cudd_bddExistAbstract, Cudd_bddIthVar, Cudd_bddOr,
    Cudd_bddSwapVariables,
};

#[cfg(feature = "visualize")]
use cudd_sys::cudd::Cudd_DumpDot;

// Re-export the CUDD constants
pub use cudd_sys::cudd::{CUDD_CACHE_SLOTS, CUDD_UNIQUE_SLOTS};

use super::{Bdd, BddManager};

type InternalCuddDD = *mut cudd_sys::DdNode;

/// BDD type for CUDD BDDs
pub struct CuddDD {
    mgr: InternalCuddMgr,
    node: InternalCuddDD,
}

impl CuddDD {
    fn new(mgr: InternalCuddMgr, node: InternalCuddDD) -> Self {
        assert!(!node.is_null());

        unsafe { Cudd_Ref(node) };

        CuddDD { mgr, node }
    }
}

impl Clone for CuddDD {
    fn clone(&self) -> Self {
        unsafe { Cudd_Ref(self.node) };
        Self {
            mgr: self.mgr.clone(),
            node: self.node,
        }
    }
}

impl Drop for CuddDD {
    fn drop(&mut self) {
        assert!(!self.node.is_null());
        unsafe { Cudd_RecursiveDeref(self.mgr.0, self.node) };
    }
}

impl PartialEq for CuddDD {
    // Two bdds `a` and `b` are equal iff: (a <=> b).is_sat() & !(a <=> b).is_unsat()
    fn eq(&self, other: &Self) -> bool {
        let eq = self.equiv(other);
        eq.satisfiable() && !eq.not().satisfiable()
    }
}

impl Debug for CuddDD {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CUDD Debug Info: ")?;
        unsafe { Cudd_PrintDebug(self.mgr.0, self.node, 0, 10) };
        write!(f, ", Node Addr: {:#?}", self.node)
    }
}

impl Display for CuddDD {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe { Cudd_PrintMinterm(self.mgr.0, self.node) };
        Ok(())
    }
}

impl Bdd for CuddDD {
    fn and(&self, rhs: &Self) -> Self {
        assert!(self.mgr == rhs.mgr);

        let new_node = unsafe { Cudd_bddAnd(self.mgr.0, self.node, rhs.node) };
        Self::new(self.mgr.clone(), new_node)
    }

    fn or(&self, rhs: &Self) -> Self {
        assert!(self.mgr == rhs.mgr);

        let new_node = unsafe { Cudd_bddOr(self.mgr.0, self.node, rhs.node) };
        CuddDD::new(self.mgr.clone(), new_node)
    }

    fn not(&self) -> Self {
        let new_node = unsafe { Cudd_Not(self.node) };
        Self::new(self.mgr.clone(), new_node)
    }

    fn exists<'a, I: IntoIterator<Item = &'a Self>>(&'a self, vars: I) -> Self {
        let mut vars = vars
            .into_iter()
            .map(|dd| {
                assert!(self.mgr == dd.mgr);
                dd.node
            })
            .collect::<Vec<_>>();

        let cube = unsafe {
            Cudd_bddComputeCube(
                self.mgr.0,
                vars.as_mut_ptr(),
                null::<i32>() as _,
                vars.len() as _,
            )
        };
        let cube = CuddDD::new(self.mgr.clone(), cube);

        let exist_node = unsafe { Cudd_bddExistAbstract(self.mgr.0, self.node, cube.node) };
        CuddDD::new(self.mgr.clone(), exist_node)
    }

    fn satisfiable(&self) -> bool {
        let n = unsafe { Cudd_CountPathsToNonZero(self.node) };
        n > 0.0
    }

    fn implies(&self, other: &Self) -> Self {
        // no built in support, construct manually
        (self.not()).or(other)
    }

    fn equiv(&self, other: &Self) -> Self {
        // no built in support, construct manually
        (self.and(other)).or(&self.not().and(&other.not()))
    }

    fn swap<'a, I: IntoIterator<Item = &'a Self>>(&'a self, from: I, to: I) -> Self {
        let mut from = from
            .into_iter()
            .map(|dd| {
                assert!(dd.mgr == self.mgr);
                dd.node
            })
            .collect::<Vec<_>>();

        let mut to = to
            .into_iter()
            .map(|bdd| {
                assert!(bdd.mgr == self.mgr);
                bdd.node
            })
            .collect::<Vec<_>>();

        assert!(to.len() == from.len(), "Invalid permutation handed to CUDD");

        let new_node = unsafe {
            Cudd_bddSwapVariables(
                self.mgr.0,
                self.node,
                from.as_mut_ptr(),
                to.as_mut_ptr(),
                from.len() as _,
            )
        };

        CuddDD::new(self.mgr.clone(), new_node)
    }
}

/// Internal Handler around the pointer to the CUDD Manager object
#[derive(PartialEq)]
struct InternalCuddMgrPtr(*mut cudd_sys::DdManager);

impl InternalCuddMgrPtr {
    /// Create a new CUDD manager with default configuration
    fn new() -> Self {
        Self::new_with_config(&CuddManagerConfig::default())
    }

    /// Create a new CUDD manager with the given configuration
    fn new_with_config(config: &CuddManagerConfig) -> Self {
        let mgr = unsafe {
            Cudd_Init(
                config.num_vars as _,
                config.num_vars_z as _,
                config.num_slots as _,
                config.cache_slots as _,
                config.max_memory as _,
            )
        };

        assert!(!mgr.is_null(), "Failed to create CUDD Manager");

        // enable reordering
        let reorder_method = config.reorder_method.into();
        unsafe { cudd_sys::cudd::Cudd_AutodynEnable(mgr, reorder_method) };

        InternalCuddMgrPtr(mgr)
    }
}

// Quit the actual CUDD manager when the `InternalCuddMgrPtr` is dropped
impl Drop for InternalCuddMgrPtr {
    fn drop(&mut self) {
        unsafe { Cudd_Quit(self.0) };
    }
}

/// Internal representation of the CUDD manager
type InternalCuddMgr = Rc<InternalCuddMgrPtr>;

/// Configuration for the CUDD manager
///
/// The documentation for these struct values has been taken from the CUDD user's manual
///
/// See for example <http://web.mit.edu/sage/export/tmp/y/usr/share/doc/polybori/cudd/node3.html>
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub struct CuddManagerConfig {
    /// It is the initial number of variables for BDDs and ADDs. If the total number of variables needed by the application is known, then it is slightly more efficient to create a manager with that number of variables. If the number is unknown, it can be set to 0, or to any other lower bound on the number of variables. Requesting more variables than are actually needed is not incorrect, but is not efficient.
    /// Default value: 0
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_num_vars"))]
    pub num_vars: usize,
    /// It is the initial number of variables for ZDDs.
    /// Default value: 0
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_num_vars_z"))]
    pub num_vars_z: usize,
    /// Determines the initial size of each subtable of the unique table. There is a subtable for each variable. The size of each subtable is dynamically adjusted to reflect the number of nodes. It is normally O.K. to use the default value for this parameter, which is CUDD_UNIQUE_SLOTS.
    /// Default value: `CUDD_UNIQUE_SLOTS`.
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_num_slots"))]
    pub num_slots: usize,
    /// It is the initial size (number of entries) of the cache.  
    /// Default value: `CUDD_CACHE_SLOTS`.
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_cache_slots"))]
    pub cache_slots: usize,
    /// It is the target value for the maximum memory occupation (in bytes). The package uses this value to decide two parameters.
    ///     - the maximum size to which the cache will grow, regardless of the hit rate or the size of the unique table.  
    ///     - the maximum size to which growth of the unique table will be preferred to garbage collection.
    /// Default value: 0
    #[cfg_attr(feature = "config_deserialize", serde(default = "default_max_memory"))]
    pub max_memory: usize,
    /// Reordering method to be used by the CUDD manager
    /// Default value: `CuddReorderMethod::Sift`
    #[cfg_attr(
        feature = "config_deserialize",
        serde(default = "default_reorder_method")
    )]
    pub reorder_method: CuddReorderMethod,
}

/// Function to get default num vars for the CUDD manager
fn default_num_vars() -> usize {
    0
}

/// Function to get default num vars for the CUDD manager
fn default_num_vars_z() -> usize {
    0
}

/// Function to get default num slots for the CUDD manager
fn default_num_slots() -> usize {
    CUDD_UNIQUE_SLOTS as usize
}
/// Function to get default cache slots for the CUDD manager
fn default_cache_slots() -> usize {
    CUDD_CACHE_SLOTS as usize
}

/// Function to get default max memory for the CUDD manager
fn default_max_memory() -> usize {
    0
}

/// Function to get default reordering method for the CUDD manager
fn default_reorder_method() -> CuddReorderMethod {
    CuddReorderMethod::Sift
}

impl Default for CuddManagerConfig {
    fn default() -> Self {
        Self {
            num_vars: default_num_vars(),
            num_vars_z: default_num_vars_z(),
            num_slots: default_num_slots(),
            cache_slots: default_cache_slots(),
            max_memory: default_max_memory(),
            reorder_method: default_reorder_method(),
        }
    }
}

/// Dynamic reordering methods supported by the CUDD manager
///
/// The documentation for these enum values has been taken from the CUDD user's manual
///
/// See for example <http://web.mit.edu/sage/export/tmp/y/usr/share/doc/polybori/cudd/node3.html>
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "config_deserialize", derive(Deserialize))]
pub enum CuddReorderMethod {
    /// Disable reordering in the CUDD library
    Disabled,
    /// `CUDD_REORDER_RANDOM`
    Random,
    /// `CUDD_REORDER_RANDOM_PIVOT`
    RandomPivot,
    /// `CUDD_REORDER_SIFT`
    Sift,
    /// `CUDD_REORDER_SIFT_CONVERGE`
    SiftConverge,
    /// `CUDD_REORDER_SYMM_SIFT`
    SymmSift,
    /// `CUDD_REORDER_SYMM_SIFT_CONV`
    SymmSiftConverge,
    /// `CUDD_REORDER_WINDOW2`
    Window2,
    /// `CUDD_REORDER_WINDOW3`
    Window3,
    /// `CUDD_REORDER_WINDOW4`
    Window4,
    /// `CUDD_REORDER_WINDOW2_CONV`
    Window2Converge,
    /// `CUDD_REORDER_WINDOW3_CONV`
    Window3Converge,
    /// `CUDD_REORDER_WINDOW4_CONV`
    Window4Converge,
    /// `CUDD_REORDER_ANNEALING`
    Annealing,
    /// `CUDD_REORDER_GENETIC`
    Genetic,
    /// `CUDD_REORDER_EXACT`
    Exact,
}

impl From<CuddReorderMethod> for cudd_sys::cudd::Cudd_ReorderingType {
    fn from(val: CuddReorderMethod) -> cudd_sys::cudd::Cudd_ReorderingType {
        match val {
            CuddReorderMethod::Disabled => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_NONE,
            CuddReorderMethod::Random => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_RANDOM,
            CuddReorderMethod::RandomPivot => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_RANDOM_PIVOT
            }
            CuddReorderMethod::Sift => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_SIFT,
            CuddReorderMethod::SiftConverge => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_SIFT_CONVERGE
            }
            CuddReorderMethod::SymmSift => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_SYMM_SIFT
            }
            CuddReorderMethod::SymmSiftConverge => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_SYMM_SIFT_CONV
            }
            CuddReorderMethod::Window2 => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_WINDOW2,
            CuddReorderMethod::Window3 => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_WINDOW3,
            CuddReorderMethod::Window4 => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_WINDOW4,
            CuddReorderMethod::Window2Converge => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_WINDOW2_CONV
            }
            CuddReorderMethod::Window3Converge => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_WINDOW3_CONV
            }
            CuddReorderMethod::Window4Converge => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_WINDOW4_CONV
            }
            CuddReorderMethod::Annealing => {
                cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_ANNEALING
            }
            CuddReorderMethod::Genetic => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_GENETIC,
            CuddReorderMethod::Exact => cudd_sys::cudd::Cudd_ReorderingType::CUDD_REORDER_EXACT,
        }
    }
}

/// Manager type for CUDD Decision Diagrams
///
/// This manager internally uses the [CUDD](https://github.com/ivmai/cudd)
/// library to create and manipulate BDDs.
///
/// Note that this manager uses unsafe code to interact with the CUDD library.
pub struct CuddManager {
    /// CUDD manager object
    mgr: InternalCuddMgr,
    /// Index of the next variable to be created
    next_var_index: Rc<Mutex<usize>>,
}

impl CuddManager {
    pub fn new() -> Self {
        let mgr = InternalCuddMgrPtr::new();

        CuddManager {
            mgr: Rc::new(mgr),
            next_var_index: Rc::new(Mutex::new(0)),
        }
    }

    pub fn new_with_config(cfg: &CuddManagerConfig) -> Self {
        let mgr = InternalCuddMgrPtr::new_with_config(cfg);

        CuddManager {
            mgr: Rc::new(mgr),
            next_var_index: Rc::new(Mutex::new(0)),
        }
    }
}

impl Default for CuddManager {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for CuddManager {
    /// Clone of a CUDD manager creates a shallow copy of the manager
    ///
    /// It does therefore not clone the CUDD manager itself, all modifications
    /// to the manager and BDDs will be reflected in all clones.
    fn clone(&self) -> Self {
        CuddManager {
            mgr: Rc::clone(&self.mgr),
            next_var_index: Rc::clone(&self.next_var_index),
        }
    }
}

impl PartialEq for CuddManager {
    /// Two CUDD managers are equal if they share the same CUDD manager object
    fn eq(&self, other: &Self) -> bool {
        self.mgr == other.mgr
    }
}

impl Debug for CuddManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "CUDD manager Info: ")?;
        unsafe { Cudd_PrintInfo(self.mgr.0, libc_stdhandle::stdout()) };
        writeln!(
            f,
            "Mgr Addr: {:#?}, Number of variables: {}",
            self.mgr.0,
            self.next_var_index.lock().unwrap()
        )
    }
}

impl BddManager for CuddManager {
    type DD = CuddDD;

    fn new_var(&mut self) -> Self::DD {
        let mut index = self.next_var_index.lock().unwrap();
        let new_node = unsafe { Cudd_bddIthVar(self.mgr.0, *index as i32) };
        *index += 1;

        CuddDD::new(self.mgr.clone(), new_node)
    }

    fn get_bdd_false(&self) -> Self::DD {
        let new_node = unsafe { Cudd_ReadLogicZero(self.mgr.0) };

        CuddDD::new(self.mgr.clone(), new_node)
    }

    fn get_bdd_true(&self) -> Self::DD {
        let new_node = unsafe { Cudd_ReadOne(self.mgr.0) };

        CuddDD::new(self.mgr.clone(), new_node)
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
        let res;
        let (bdds_to_be_dumped, bdd_names) = bdd_names
            .into_iter()
            .map(|(dd, dn)| (dd.node, CString::new(dn.to_string()).unwrap()))
            .collect::<(Vec<_>, Vec<_>)>();

        let variable_names = variable_names
            .into_iter()
            .map(|(_, vn)| CString::new(vn.to_string()).unwrap())
            .collect::<Vec<_>>();

        if variable_names.len() < *self.next_var_index.lock().unwrap() && !variable_names.is_empty()
        {
            return Err(std::io::Error::other(
                "Number of variable names does not match number of variables! Aborting as this will lead to a segfault",
            ));
        }

        unsafe {
            let file = libc::fdopen(file.as_raw_fd(), "w".as_ptr() as _);

            let bdd_names = bdd_names
                .into_iter()
                .map(|n| n.into_raw())
                .collect::<Vec<_>>();

            let mut var_names_ptr = null();

            let var_names = variable_names
                .into_iter()
                .map(|n| n.into_raw())
                .collect::<Vec<_>>();

            if !var_names.is_empty() {
                var_names_ptr = var_names.as_ptr() as *const *const i8;
            }

            res = Cudd_DumpDot(
                self.mgr.0,
                bdds_to_be_dumped.len() as i32,
                bdds_to_be_dumped.as_ptr() as *mut *mut cudd_sys::DdNode,
                var_names_ptr,
                bdd_names.as_ptr() as *const *const i8,
                file,
            );

            libc::fflush(file);

            let _ = var_names.into_iter().map(|p| CString::from_raw(p));
            let _ = bdd_names.into_iter().map(|p| CString::from_raw(p));
        };

        if res == 1 {
            Ok(())
        } else {
            Err(std::io::Error::other("Failed to dump DOT file"))
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        BddManager,
        bdd_test_utils::{self, test_mgr_eq_and_clone},
    };

    use super::{CuddManager, CuddManagerConfig, CuddReorderMethod};

    #[test]
    fn test_mgr_eq() {
        let mgr1 = CuddManager::default();
        let mgr2 = CuddManager::default();

        test_mgr_eq_and_clone(mgr1, mgr2);
    }

    #[test]
    fn test_mgr_get() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_mgr_get(mgr)
    }

    #[test]
    fn test_not() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_not(mgr)
    }

    #[test]
    fn test_and() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_and(mgr)
    }

    #[test]
    fn test_or() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_or(mgr)
    }

    #[test]
    fn test_exists() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_exists(mgr)
    }

    #[test]
    fn test_implies() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_implies(mgr)
    }

    #[test]
    fn test_equiv() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_equiv(mgr)
    }

    #[test]
    fn test_swap() {
        let mgr = CuddManager::default();
        bdd_test_utils::test_swap(mgr)
    }

    #[test]
    fn test_manager_with_custom_config() {
        let cfg = CuddManagerConfig {
            num_vars: 10,
            num_vars_z: 0,
            num_slots: 1000,
            cache_slots: 1000,
            max_memory: 0,
            reorder_method: CuddReorderMethod::Disabled,
        };

        let mgr = CuddManager::new_with_config(&cfg);

        bdd_test_utils::test_mgr_get(mgr.clone());
        bdd_test_utils::test_not(mgr.clone());
        bdd_test_utils::test_and(mgr.clone());
        bdd_test_utils::test_or(mgr.clone());
        bdd_test_utils::test_exists(mgr.clone());
    }

    #[test]
    #[should_panic]
    fn test_panic_on_bdd_of_mixed_mgrs() {
        let mgr1 = CuddManager::default();
        let mgr2 = CuddManager::default();
        bdd_test_utils::panic_on_bdd_of_mixed_mgrs(mgr1, mgr2)
    }

    #[test]
    fn print_funcs_work() {
        let mut mgr = CuddManager::new();
        let v = mgr.new_var();

        println!("Var: {v}, Debug: {v:?}");
        println!("Mgr Debug: {mgr:?}");
    }

    #[cfg(feature = "visualize")]
    #[test]
    fn test_abort_if_not_enough_var_names() {
        let mut mgr = CuddManager::default();
        let bdd1 = mgr.new_var();
        let _ = mgr.new_var();

        let file = std::fs::File::create("test.dot").unwrap();

        let res = mgr.dump_dot(file, vec![(&bdd1, "BDD1")], vec![(&bdd1, "Var1")]);

        assert!(res.is_err());
    }
}

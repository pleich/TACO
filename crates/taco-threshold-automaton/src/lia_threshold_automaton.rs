//! A linear arithmetic threshold automaton or [`LIAThresholdAutomaton`]
//! is a threshold automaton containing linear arithmetic guards. The
//! goal of the [`LIAThresholdAutomaton`] is to stay as close to the formal
//! definition of a threshold automaton as possible.
//!
//! To convert a [`GeneralThresholdAutomaton`] to a [`LIAThresholdAutomaton`]
//! all guards are translated into one of these forms:
//! - [`SingleAtomConstraint`]: Which represents a threshold in the form
//!   `x <COMPARISON_OP> c_1 * p_1 + ... c_n * p_n + c`
//!   where `c_1, ..., c_n, c` are rational constants, `p_1, ..., p_n` are
//!   Parameters and x is a single shared variable.
//! - [`SumAtomConstraint`]: Represents a threshold of the form
//!   `cx_1 * x_1 + ... + cx_m * x_m <COMPARISON_OP> c_1 * p_1 + ... c_n * p_n + c`
//!   where `c_1, ..., c_n, cx_1, ..., cx_m, c` are rational constants, `p_1,
//!   ..., p_n` are Parameters and x_1, ..., x_m are shared variables.
//!   Additionally, all coefficients `cx_1, ..., cx_m` must be all positive.
//! - [`ComparisonConstraint`]: Comparison constraints are structured analog to
//!   a [`SumAtomConstraint`], but allow mixing positive and negative constants
//!   in the constants `cx_1, ..., cx_m`.
//!
//! Note that not all algorithms support all types of guards. Especially the
//! [`ComparisonConstraint`] makes the verification problem undecidable (even without
//! decrements and or resets). For more information see:
//!     
//! > All Flavors of Threshold Automata - Jure Kukovec, Igor Konnov,
//! > Josef Widder - <https://doi.org/10.4230/LIPIcs.CONCUR.2018.19>

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use crate::expressions::{Atomic, BooleanConnective, BooleanExpression, Location, Variable};

use crate::general_threshold_automaton::{Action, GeneralThresholdAutomaton, Rule};
use crate::lia_threshold_automaton::integer_thresholds::{ThresholdConstraintOver, WeightedSum};

pub mod general_to_lia;
pub mod integer_thresholds;
pub mod no_sum_var_ta;
pub mod properties;

/// A linear arithmetic threshold automaton or [`LIAThresholdAutomaton`]
/// is a threshold automaton containing linear arithmetic guards. The
/// goal of the [`LIAThresholdAutomaton`] is to stay as close to the formal
/// definition of a threshold automaton as possible.
///
/// To convert a [`GeneralThresholdAutomaton`] to a [`LIAThresholdAutomaton`]
/// all guards are translated into one of these forms:
/// - [`SingleAtomConstraint`]: Which represents a threshold in the form
///   `x <COMPARISON_OP> c_1 * p_1 + ... c_n * p_n + c`
///   where `c_1, ..., c_n, c` are rational constants, `p_1, ..., p_n` are
///   Parameters and x is a single shared variable.
/// - [`SumAtomConstraint`]: Represents a threshold of the form
///   `cx_1 * x_1 + ... + cx_m * x_m <COMPARISON_OP> c_1 * p_1 + ... c_n * p_n + c`
///   where `c_1, ..., c_n, cx_1, ..., cx_m, c` are rational constants, `p_1,
///   ..., p_n` are Parameters and x_1, ..., x_m are shared variables.
///   Additionally, all coefficients `cx_1, ..., cx_m` must be all positive.
/// - [`ComparisonConstraint`]: Comparison constraints are structured analog to
///   a [`SumAtomConstraint`], but allow mixing positive and negative constants in
///   the constants `cx_1, ..., cx_m`.
///
/// Note that not all algorithms support all types of guards. Especially the
/// [`ComparisonConstraint`] makes the verification problem undecidable (even without
/// decrements and or resets). For more information see:
///     
/// > All Flavors of Threshold Automata - Jure Kukovec, Igor Konnov,
/// > Josef Widder - <https://doi.org/10.4230/LIPIcs.CONCUR.2018.19>
#[derive(Debug, PartialEq, Clone)]
pub struct LIAThresholdAutomaton {
    /// [`GeneralThresholdAutomaton`] the canonical automaton has been constructed from
    ta: GeneralThresholdAutomaton,
    /// Initial conditions on variables in linear arithmetic
    init_variable_constr: Vec<LIAVariableConstraint>,
    /// Transition rules of the threshold automaton indexed by source location
    rules: HashMap<Location, Vec<LIARule>>,
    /// Additional variables that are used to replace sums
    /// TODO: remove when a proper ordering for sums of variables is implemented
    additional_vars_for_sums: HashMap<Variable, WeightedSum<Variable>>,
}

/// Rule type of [`LIAThresholdAutomaton`]
///
/// A rule guarded by a constraint representable in linear arithmetic (see
/// [`LIAVariableConstraint`]).
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct LIARule {
    /// Id assigned to the rule in the specification
    id: u32,
    /// Source location of the rule
    source: Location,
    /// Target location of the rule
    target: Location,
    /// Guard of the rule
    guard: LIAVariableConstraint,
    /// Effect of the rule
    actions: Vec<Action>,
}

/// Errors that can occur when trying to transform a threshold automaton in a
/// linear arithmetic threshold automaton
#[derive(Debug, Clone, PartialEq)]
pub enum LIATransformationError {
    /// Error occurred during transformation of a guard of a rule, see
    /// [`ConstraintRewriteError`] for more details on the error
    GuardError(
        Box<Rule>,
        Box<BooleanExpression<Variable>>,
        Box<ConstraintRewriteError>,
    ),
    /// Error occurred during the transformation of an initial variable
    /// constraint, see [`ConstraintRewriteError`] for more details on the error
    InitialConstraintError(
        Box<BooleanExpression<Variable>>,
        Box<ConstraintRewriteError>,
    ),
}

/// Abstract constraint type for linear arithmetic formulas over shared
/// variables
///  
/// This struct allows to represent combinations the different types of
/// constraints over evaluations of shared variables. It allows to reference:
///
/// - [`SingleAtomConstraint`]: Which represents a threshold in the form
///   `x <COMPARISON_OP> c_1 * p_1 + ... c_n * p_n + c`
///   where `c_1, ..., c_n, c` are rational constants, `p_1, ..., p_n` are
///   Parameters and x is a single shared variable.
/// - [`SumAtomConstraint`]: Represents a threshold of the form
///   `cx_1 * x_1 + ... + cx_m * x_m <COMPARISON_OP> c_1 * p_1 + ... c_n * p_n + c`
///   where `c_1, ..., c_n, cx_1, ..., cx_m, c` are rational constants, `p_1,
///   ..., p_n` are Parameters and x_1, ..., x_m are shared variables.
///   Additionally, all coefficients `cx_1, ..., cx_m` must be all positive.
/// - [`ComparisonConstraint`]: Comparison constraints are structured analog to
///   a [`SumAtomConstraint`], but allow mixing positive and negative constants in
///   the constants `cx_1, ..., cx_m`.
///
/// and boolean combinations of these guards
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LIAVariableConstraint {
    /// Constraint over the difference between variables / comparing variables
    ComparisonConstraint(ComparisonConstraint<Variable>),
    /// Constraint over a single variable
    SingleVarConstraint(SingleAtomConstraint<Variable>),
    /// Constraint over the sum of multiple variables
    SumVarConstraint(SumAtomConstraint<Variable>),
    /// Boolean Combination of multiple constraints over variables
    BinaryGuard(
        Box<LIAVariableConstraint>,
        BooleanConnective,
        Box<LIAVariableConstraint>,
    ),
    /// True / always enabled
    True,
    /// False / always disabled
    False,
}

/// Error that can occur during the transformation of a guard
#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintRewriteError {
    /// Constraint is not a linear arithmetic constraint (e.g. it could contain
    /// multiplications of atoms)
    NotLinearArithmetic,
    /// Constraint over parameters values instead of shared memory values
    ///
    /// Constraints like this should be part of the resilience condition
    ParameterConstraint(Box<BooleanExpression<Variable>>),
}

/// Threshold guard over a single atom
///
/// This struct represents a guard over a single atom, i.e., it represents a
/// constraint formula of the form `v COMPOP cp_1 * p_1 + ... + cp_n * p_m + c`
/// where `cp_1, ..., cp_m` are rational factors, `COMPOP` is a comparison
/// operator (i.e.,`<, >, <=, >=, ==, !=`), `v` is a atom, `p_1, ..., p_m`
/// are parameters, and `c` is a rational constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SingleAtomConstraint<T: Atomic>(ThresholdConstraintOver<T>);

/// Error that can occur when trying to construct a [`SingleAtomConstraint`]
#[derive(Debug, Clone, PartialEq)]
pub enum SingleAtomConstrExtractionError {
    /// The constraint references multiple atoms, it could be a
    /// [`SumAtomConstraint`] or [`ComparisonConstraint`]
    HasMultipleAtoms,
    /// Rewriting of the constraint failed
    TransformationFailed(ConstraintRewriteError),
}

/// Constraint over the evaluation over a sum of multiple atoms
///
/// This struct represents a guard over the values of a sum of atoms, i.e., it
/// represents a constraint formula of the form
/// `cv_1 * v_1 + ... + cv_n * v_n <COMPOP> cp_1 * p_1 + ... + cp_n * p_m + c`
/// where `cv_1, ..., cv_n, cp_1, ..., cp_m` are rational factors, `COMPOP` is
/// a comparison operator (i.e.,`<, >, <=, >=, ==, !=`), `v_1, ..., v_n` are
/// variables, `p_1, ..., p_m` are parameters, and `c` is a rational constant.
///
/// Additionally, all variable coefficients, i.e., `cv_1, ..., cv_n`, must be
/// greater than zero.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SumAtomConstraint<T: Atomic>(ThresholdConstraintOver<WeightedSum<T>>);

/// Error that can occur during the creation of a [`SumAtomConstraint`]
#[derive(Debug, Clone, PartialEq)]
pub enum SumVarConstraintCreationError {
    /// Guard is a [`ComparisonConstraint`] not a [`SumAtomConstraint`]
    IsComparisonConstraint,
    /// Guard is a [`SingleAtomConstraint`] not a [`SumAtomConstraint`]
    IsSingleAtomConstraint,
}

/// Constraint over the difference between atoms / comparing atoms
///
/// This struct represents a comparison guard, i.e., it represents a guard of
/// the form
/// `cv_1 * v_1 + ... + cv_n * v_n <COMPOP> cp_1 * p_1 + ... + cp_n * p_m + c`
/// where `cv_1, ..., cv_n, cp_1, ..., cp_m` are rational factors, `<COMPOP>` is
/// a comparison operator (i.e.,`<, >, <=, >=, ==, !=`), `v_1, ..., v_n` are
/// atoms, `p_1, ..., p_m` are parameters, and `c` is a rational constant.
///
/// Additionally, at least one of the atom coefficients, i.e.,
/// `cv_1, ..., cv_n`, must be smaller than zero and at least one greater than
/// zero. Otherwise the guard would be a [`SumAtomConstraint`].
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ComparisonConstraint<T: Atomic>(ThresholdConstraintOver<WeightedSum<T>>);

/// Error that can occur during the creation of a comparison guard
#[derive(Debug, Clone, PartialEq)]
pub enum ComparisonConstraintCreationError {
    /// Guard is a [`SumAtomConstraint`] not a [`ComparisonConstraint`]
    IsSumVarConstraint,
}

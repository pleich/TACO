//! A library to interact with threshold automata
//!
//! This crate contains the definitions of the types used to represent and
//! interact with threshold automata. In particular, it contains the
//! traits:
//! - [`ThresholdAutomaton`]: common interface for all flavors of threshold
//!   automata
//! - [`RuleDefinition`]: common interface for rules in a threshold automaton
//! - [`ActionDefinition`]: trait to represent different flavors of actions

//! - [`VariableConstraint`]: different forms of constraints over variables
//!
//! The most general type implementing the interface is the
//! [`general_threshold_automaton::GeneralThresholdAutomaton`] type. However,
//! the type is more general than the theoretical definition of threshold
//! automata, as it for example allows variable comparisons or resets.
//!
//! To the best of our knowledge, verification algorithms for threshold automata
//! only exist for threshold automata that use linear integer arithmetic in
//! their guards / thresholds. Therefore, when implementing a  new model
//! checker, you will usually want to work with the
//! [`lia_threshold_automaton::LIAThresholdAutomaton`] flavor of threshold
//! automata.

use std::fmt::Debug;
use std::{fmt, hash::Hash};

use expressions::{BooleanExpression, IntegerExpression, Location, Parameter, Variable};

use crate::expressions::IsDeclared;

pub mod expressions;
pub mod general_threshold_automaton;
pub mod lia_threshold_automaton;

pub mod path;

#[cfg(feature = "dot")]
pub mod dot;

/// Constraint over the number of processes in a certain location
pub type LocationConstraint = BooleanExpression<Location>;

/// Constraint over the valuation of parameters
pub type ParameterConstraint = BooleanExpression<Parameter>;

/// Constraint over the valuation of the shared variables
pub type BooleanVarConstraint = BooleanExpression<Variable>;

/// Common trait for different types of threshold automata
///
/// This trait is implemented by all types and flavors of threshold
/// automata and provides a common interface for interacting with threshold
/// automata.
///
/// This trait is for example implemented by
/// [`general_threshold_automaton::GeneralThresholdAutomaton`]
/// or [`lia_threshold_automaton::LIAThresholdAutomaton`].
pub trait ThresholdAutomaton:
    Debug + Clone + fmt::Display + IsDeclared<Parameter> + IsDeclared<Variable> + IsDeclared<Location>
{
    /// Type of the rules of the threshold automaton
    type Rule: RuleDefinition;
    /// Type of the initial variable conditions of the threshold automaton
    type InitialVariableConstraintType: VariableConstraint;

    /// Get the name of the threshold automaton
    fn name(&self) -> &str;

    /// Get the parameters of the threshold automaton
    fn parameters(&self) -> impl Iterator<Item = &Parameter>;

    /// Get the initial location constraints of the threshold automaton
    fn initial_location_constraints(&self) -> impl Iterator<Item = &LocationConstraint>;

    /// Get the initial variable constraints of the threshold automaton
    fn initial_variable_constraints(
        &self,
    ) -> impl Iterator<Item = &Self::InitialVariableConstraintType>;

    /// Get the resilience condition of the threshold automaton
    fn resilience_conditions(&self) -> impl Iterator<Item = &BooleanExpression<Parameter>>;

    /// Get the shared variables of the threshold automaton
    fn variables(&self) -> impl Iterator<Item = &Variable>;

    /// Get the locations of the threshold automaton
    fn locations(&self) -> impl Iterator<Item = &Location>;

    /// Check if a location can be initial by the location constraints of the
    /// threshold automaton
    ///
    /// Returns true if the location can be an initial location of the threshold
    fn can_be_initial_location(&self, location: &Location) -> bool;

    /// Get the rules of the threshold automaton
    fn rules(&self) -> impl Iterator<Item = &Self::Rule>;

    /// Get incoming rules to a location
    ///
    /// Returns the rules that have the given location as target location.
    /// This means that the location is the target of the transition.
    fn incoming_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule>;

    /// Get outgoing rules for a location
    ///
    /// Returns the rules that have the given location as source location.
    fn outgoing_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule>;

    /// Check whether the threshold automaton contains any decrements or resets
    fn has_decrements_or_resets(&self) -> bool {
        self.rules().any(|r| r.has_decrements() || r.has_resets())
    }

    /// Check whether the threshold automaton contains any decrements
    fn has_decrements(&self) -> bool {
        self.rules().any(|r| r.has_decrements())
    }

    /// Check whether the threshold automaton contains any resets
    fn has_resets(&self) -> bool {
        self.rules().any(|r| r.has_resets())
    }
}

/// Trait implemented by all flavors of rules
///
/// Trait for common functionality of rules. This trait is implemented for
/// the [`general_threshold_automaton::Rule`] type for
/// [`general_threshold_automaton::GeneralThresholdAutomaton`] and
/// [`lia_threshold_automaton::LIARule`] for
/// [`lia_threshold_automaton::LIAThresholdAutomaton`].
pub trait RuleDefinition: Clone + Debug + fmt::Display + PartialEq + Hash + Eq {
    /// Type of the actions of the rule
    type Action: ActionDefinition;
    /// Type of the guard of the rule
    type Guard: VariableConstraint;

    /// Returns the id of the rule
    ///
    /// The id is a unique identifier assigned to the rule in the specification.
    /// It is used to refer to the rule in the specification.
    fn id(&self) -> u32;

    /// Returns the source location of the rule
    ///
    /// The source location is the location from which the rule transitions
    /// to the target location.
    fn source(&self) -> &Location;

    /// Returns the target location of the rule
    ///
    /// The target location is the location to which the rule transitions
    /// from the source location.
    fn target(&self) -> &Location;

    /// Returns the guard of the rule
    ///
    /// The guard is a boolean expression over shared variables that must be
    /// satisfied for the rule to be enabled.
    fn guard(&self) -> &Self::Guard;

    /// Returns the actions of the rule
    ///
    /// The actions are the updates to shared variables that are performed
    /// when the rule is executed.
    fn actions(&self) -> impl Iterator<Item = &Self::Action>;

    /// Check whether the rule has a decrement action
    fn has_decrements(&self) -> bool {
        self.actions().any(|ac| ac.is_decrement())
    }

    /// Check whether the rule has a reset action
    fn has_resets(&self) -> bool {
        self.actions().any(|ac| ac.is_reset())
    }
}

/// Trait implemented by all flavors of actions
///
/// This trait is for example implemented for the
/// [`general_threshold_automaton::Action`] type.
pub trait ActionDefinition: Clone + Debug + fmt::Display + PartialEq + Hash + Eq + Ord {
    /// Returns the variable to be updated by the action
    fn variable(&self) -> &Variable;

    /// Check whether the action does not change any variables, i.e. is a noop
    fn is_unchanged(&self) -> bool;

    /// Check whether the action is a reset action
    fn is_reset(&self) -> bool;

    /// Check whether the action is an increment action
    fn is_increment(&self) -> bool;

    /// Check whether the action is a decrement action
    fn is_decrement(&self) -> bool;
}

/// Trait implemented by all flavors of constraints over variables that can
/// serve as Guards
///
/// This trait is for example implemented by [`BooleanExpression<Variable>`] or
/// [`lia_threshold_automaton::LIAVariableConstraint`]
pub trait VariableConstraint: Clone + Debug + fmt::Display + PartialEq + Ord {
    /// Get the guard as a boolean expression over variables
    fn as_boolean_expr(&self) -> BooleanExpression<Variable>;
}

/// Trait for threshold automata that can be modified
///
/// This trait is implemented by threshold automata that can be modified.
/// for example, through preprocessing or other means. It provides methods to
/// modify, remove or add components of the threshold automaton.
///
/// Note the resulting threshold automaton is not validated. It is up to the
/// user to ensure that transformations result in a valid threshold automaton.
/// Invalid threshold automata can lead to panics of other methods or functions.
/// If a type does not implement this trait, you should modify a higher level
/// representation.
///
/// Methods from this trait should not be used to construct a threshold
/// automaton, but rather to modify an existing one. To build a threshold
/// automaton, use the corresponding builder, e.g.,
/// [`general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder`].
pub trait ModifiableThresholdAutomaton: ThresholdAutomaton {
    /// Rename the threshold automaton
    fn set_name(&mut self, new_name: String);

    /// Add a new rule to the threshold automaton
    ///
    /// **Note**: The rule that is inserted is not validated. To build a threshold
    /// automaton, you should use the corresponding builder, e.g.,
    /// `GeneralThresholdAutomatonBuilder`.
    fn add_rule(&mut self, rule: Self::Rule);

    /// Add a new resilience condition to the threshold automaton
    ///
    /// **Note**: The resilience condition that is inserted is not validated. To
    /// build a threshold automaton, you should use the corresponding builder,
    ///  e.g., `GeneralThresholdAutomatonBuilder`.
    fn add_resilience_conditions<C: IntoIterator<Item = BooleanExpression<Parameter>>>(
        &mut self,
        conditions: C,
    );

    /// Add a new initial location constraint to the threshold automaton
    ///
    /// **Note**: The initial location constraint that is inserted is not
    /// validated. To build a threshold automaton, you should use the
    /// corresponding builder, e.g., `GeneralThresholdAutomatonBuilder`.
    fn add_initial_location_constraints<C: IntoIterator<Item = LocationConstraint>>(
        &mut self,
        constraints: C,
    );

    /// Add a new initial variable constraint to the threshold automaton
    ///
    /// **Note**: The initial variable constraint that is inserted is not
    /// validated. To build a threshold automaton, you should use the
    /// corresponding builder, e.g., `GeneralThresholdAutomatonBuilder`.
    fn add_initial_variable_constraints<C: IntoIterator<Item = BooleanVarConstraint>>(
        &mut self,
        constraints: C,
    );

    /// Retains only the rules specified by the predicate.
    ///
    /// In other words, remove all rules r for which predicate(&r) returns false.
    ///
    /// **Note**: The method `predicate` can be called multiple times per rule.
    fn retain_rules<F>(&mut self, predicate: F)
    where
        F: Fn(&Self::Rule) -> bool;

    /// Apply a transformation to each rule
    ///
    /// This method is used to apply a transformation to each rule of the
    /// threshold automaton. The transformation is applied in place, meaning
    /// that the rule is modified directly.
    ///
    /// **Note**:
    /// - The method `f` can be called multiple times per rule.
    /// - The transformed rule is not validated
    fn transform_rules<F>(&mut self, f: F)
    where
        F: FnMut(&mut Self::Rule);

    /// Remove a location `location` from the threshold automaton, removes rules
    /// referencing the location and replace every occurrence in initial
    /// conditions with `subst`
    ///
    /// **Note**: The resulting location constraints are not validated
    fn remove_location_and_replace_with(
        &mut self,
        location: &Location,
        subst: IntegerExpression<Location>,
    );

    /// Remove a variable `variable` from the threshold automaton, replace every
    /// occurrence in initial conditions or guards with `subst` and remove all
    /// updates to `variable` from the rules
    ///
    /// **Note**: The resulting variable constraints and guards are not validated
    fn remove_variable_and_replace_with(
        &mut self,
        variable: &Variable,
        subst: IntegerExpression<Variable>,
    );

    /// Remove all location_constraints from the threshold automaton
    /// Needed to specify initial configurations for coverability and
    /// reachability through the CLI.
    fn replace_initial_location_constraints<C: IntoIterator<Item = LocationConstraint>>(
        &mut self,
        constraints: C,
    );

    /// Remove all variable_constraints from the threshold automaton
    /// Needed to specify initial configurations for coverability and
    /// reachability through the CLI.
    fn replace_initial_variable_constraints<C: IntoIterator<Item = BooleanVarConstraint>>(
        &mut self,
        constraints: C,
    );
}

//! Module implementing the most general form of threshold automata
//! [`GeneralThresholdAutomaton`].
//!
//! This module contains the definition of the [`GeneralThresholdAutomaton`] type,
//! which represents the most general form of a threshold automaton. This type
//! can represent any threshold automaton, including those with variable
//! comparisons, non-linear arithmetic thresholds and reset actions.
//!
//! Usually automata are expected to be parsed in to this form, and can then be
//! transformed into a more restricted form, such as for example a
//!  [`super::lia_threshold_automaton::LIAThresholdAutomaton`].

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{Debug, Display},
};

use taco_display_utils::{
    display_iterator_stable_order, indent_all, join_iterator, join_iterator_and_add_back,
};

use crate::{
    ActionDefinition, BooleanVarConstraint, LocationConstraint, ModifiableThresholdAutomaton,
    ParameterConstraint, RuleDefinition, ThresholdAutomaton, VariableConstraint,
    expressions::{
        BooleanExpression, IntegerExpression, IsDeclared, Location, Parameter, Variable,
    },
};
use std::hash::Hash;

pub mod builder;

/// Type representing a general threshold automaton that can include variable
/// comparisons, general non-linear arithmetic guards and as well as reset
/// actions.
#[derive(Debug, Eq, Clone)]
pub struct GeneralThresholdAutomaton {
    /// Name of the threshold automaton
    name: String,
    /// List of parameters appearing in the threshold automaton
    parameters: HashSet<Parameter>,
    /// List of shared variables appearing in the threshold automaton
    variables: HashSet<Variable>,
    /// List of locations appearing in the threshold automaton
    locations: HashSet<Location>,
    /// Transition rules of the threshold automaton indexed by source location
    outgoing_rules: HashMap<Location, Vec<Rule>>,
    /// Initial constraints on the number of processes in a location
    initial_location_constraint: Vec<LocationConstraint>,
    /// Initial constraint on the variable values
    initial_variable_constraint: Vec<BooleanVarConstraint>,
    /// Constraint over the parameters of the threshold automaton
    resilience_condition: Vec<ParameterConstraint>,
}

impl GeneralThresholdAutomaton {
    /// Get the threshold automaton in the ByMC format
    pub fn to_bymc(&self) -> String {
        self.to_string()
    }

    /// Returns an iterator over the initial location constraints of the threshold automaton
    pub fn initial_variable_conditions(&self) -> impl Iterator<Item = &BooleanVarConstraint> {
        self.initial_variable_constraint.iter()
    }

    /// Returns an iterator over the initial location constraints of the threshold automaton
    pub fn initial_location_conditions(&self) -> impl Iterator<Item = &LocationConstraint> {
        self.initial_location_constraint.iter()
    }

    /// Get the internal set of rules of the threshold automaton
    pub(crate) fn get_rule_map(&self) -> HashMap<Location, Vec<Rule>> {
        self.outgoing_rules.clone()
    }

    /// Returns the body of the threshold automaton, i.e. the definitions of
    /// locations, variables, rules, initial assumptions, etc. in ByMC format
    /// without the outer `proc`/ `skel`/ `thresholdAutomaton` declaration
    pub fn get_ta_body_in_bymc_format(&self) -> String {
        let variables = format!("shared {};", display_iterator_stable_order(&self.variables));
        let parameters = format!(
            "parameters {};",
            display_iterator_stable_order(self.parameters())
        );

        let rc = format!(
            "assumptions ({}) {{\n{}}}",
            self.resilience_condition.len(),
            indent_all(join_iterator_and_add_back(
                self.resilience_conditions(),
                ";\n"
            ))
        );

        let mut location_str = String::new();
        let mut locations = self.locations().collect::<Vec<_>>();
        locations.sort();

        for (i, loc) in locations.into_iter().enumerate() {
            location_str += &format!("{loc}:[{i}];\n");
        }
        let locations = format!(
            "locations ({}) {{\n{}}}",
            self.locations.len(),
            indent_all(location_str)
        );

        let initial_cond = format!(
            "inits ({}) {{\n{}}}",
            self.initial_location_constraint.len() + self.initial_variable_constraint.len(),
            indent_all(
                join_iterator_and_add_back(self.initial_location_constraints(), ";\n")
                    + &join_iterator_and_add_back(self.initial_variable_constraints(), ";\n")
            )
        );

        let mut sorted_rules_by_id = self.rules().collect::<Vec<_>>();
        sorted_rules_by_id.sort_by_key(|r| &r.id);
        let rules = format!(
            "rules ({}) {{\n{}}}",
            self.rules().count(),
            indent_all(join_iterator_and_add_back(
                sorted_rules_by_id.into_iter(),
                ";\n"
            ))
        );

        format!("{variables}\n\n{parameters}\n\n{rc}\n\n{locations}\n\n{initial_cond}\n\n{rules}")
    }
}

impl ModifiableThresholdAutomaton for GeneralThresholdAutomaton {
    fn set_name(&mut self, new_name: String) {
        self.name = new_name;
    }

    fn add_rule(&mut self, rule: Self::Rule) {
        self.outgoing_rules
            .entry(rule.source().clone())
            .or_default()
            .push(rule.clone());
    }

    fn retain_rules<F>(&mut self, predicate: F)
    where
        F: Fn(&Self::Rule) -> bool,
    {
        self.outgoing_rules
            .iter_mut()
            .for_each(|(_, rs)| rs.retain(&predicate));
        self.outgoing_rules.retain(|_, rs| !rs.is_empty());
    }

    fn transform_rules<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Self::Rule),
    {
        self.outgoing_rules.iter_mut().for_each(|(_, rs)| {
            rs.iter_mut().for_each(&mut f);
        });
    }

    fn remove_location_and_replace_with(
        &mut self,
        location: &Location,
        subst: IntegerExpression<Location>,
    ) {
        self.locations.remove(location);

        self.initial_location_constraint.iter_mut().for_each(|ic| {
            ic.substitute_atom_with(location, &subst);
        });

        self.retain_rules(|r| r.source() != location && r.target() != location);
    }

    fn remove_variable_and_replace_with(
        &mut self,
        variable: &Variable,
        subst: IntegerExpression<Variable>,
    ) {
        self.variables.remove(variable);

        self.initial_variable_constraint.iter_mut().for_each(|ic| {
            ic.substitute_atom_with(variable, &subst);
        });

        self.transform_rules(|r| {
            r.guard.substitute_atom_with(variable, &subst);
            r.actions.retain(|act| act.variable() != variable);
        });
    }

    fn add_resilience_conditions<C: IntoIterator<Item = BooleanExpression<Parameter>>>(
        &mut self,
        conditions: C,
    ) {
        self.resilience_condition.extend(conditions);
    }

    fn add_initial_location_constraints<C: IntoIterator<Item = LocationConstraint>>(
        &mut self,
        constraints: C,
    ) {
        self.initial_location_constraint.extend(constraints);
    }

    fn add_initial_variable_constraints<C: IntoIterator<Item = BooleanVarConstraint>>(
        &mut self,
        constraints: C,
    ) {
        self.initial_variable_constraint.extend(constraints);
    }

    fn replace_initial_location_constraints<C: IntoIterator<Item = LocationConstraint>>(
        &mut self,
        constraints: C,
    ) {
        self.initial_location_constraint = constraints.into_iter().collect();
    }

    fn replace_initial_variable_constraints<C: IntoIterator<Item = BooleanVarConstraint>>(
        &mut self,
        constraints: C,
    ) {
        self.initial_variable_constraint = constraints.into_iter().collect();
    }
}

impl ThresholdAutomaton for GeneralThresholdAutomaton {
    type Rule = Rule;
    type InitialVariableConstraintType = BooleanVarConstraint;

    fn name(&self) -> &str {
        self.name.as_str()
    }

    fn parameters(&self) -> impl Iterator<Item = &Parameter> {
        self.parameters.iter()
    }

    fn resilience_conditions(&self) -> impl Iterator<Item = &BooleanExpression<Parameter>> {
        self.resilience_condition.iter()
    }

    fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.variables.iter()
    }

    fn locations(&self) -> impl Iterator<Item = &Location> {
        self.locations.iter()
    }

    /// Check if the given location has an initial condition that prevents it
    /// from initially having any processes in it
    ///
    /// # Implementation
    ///
    /// Many threshold automata have initial constraints of the form
    /// `loc1 == 0`, preventing any processes from starting in `loc1` initially.
    /// This function checks if the given location has such a constraint.
    ///
    /// It will *not* attempt to evaluate all initial constraints and check
    /// (for example by using an SMT solver) if the location can be initially
    /// occupied.
    ///
    /// Instead, it will only check if the initial constraints contain a
    /// constraint of the form `loc1 == <INTEGER EXPRESSION>`, where
    /// `<INTEGER EXPRESSION>` evaluates to 0.
    ///
    /// This approach does not sacrifice correctness, as the initial constraints
    /// are anyway encoded in the SMT query.
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::*;
    /// use taco_threshold_automaton::expressions::Location;
    /// use taco_threshold_automaton::general_threshold_automaton::{GeneralThresholdAutomaton, builder::GeneralThresholdAutomatonBuilder};
    /// use taco_threshold_automaton::ThresholdAutomaton;
    /// use taco_threshold_automaton::LocationConstraint;
    /// use std::collections::HashMap;
    ///
    /// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
    ///            .with_locations(vec![
    ///                Location::new("loc1"),
    ///                Location::new("loc2"),
    ///                Location::new("loc3"),
    ///            ]).unwrap()
    ///            .initialize()
    ///            .with_initial_location_constraints(vec![
    ///                LocationConstraint::ComparisonExpression(
    ///                     Box::new(IntegerExpression::Atom(Location::new("loc1"))),
    ///                     ComparisonOp::Eq,
    ///                     Box::new(IntegerExpression::Const(0)),
    ///                 ),
    ///                 LocationConstraint::ComparisonExpression(
    ///                     Box::new(IntegerExpression::Atom(Location::new("loc2"))),
    ///                     ComparisonOp::Geq,
    ///                     Box::new(IntegerExpression::Const(0)),
    ///                 ) & LocationConstraint::ComparisonExpression(
    ///                     Box::new(IntegerExpression::Atom(Location::new("loc2"))),
    ///                     ComparisonOp::Leq,
    ///                     Box::new(IntegerExpression::Const(0)),
    ///                 ),
    ///            ]).unwrap()
    ///            .build();
    ///     
    /// assert!(!ta.can_be_initial_location(&Location::new("loc1")));
    /// assert!(!ta.can_be_initial_location(&Location::new("loc2")));
    /// assert!(ta.can_be_initial_location(&Location::new("loc3")));
    /// ```
    fn can_be_initial_location(&self, loc: &Location) -> bool {
        !self
            .initial_location_conditions()
            .any(|loc_constr| loc_constr.try_check_expr_constraints_to_zero(loc))
    }

    fn rules(&self) -> impl Iterator<Item = &Self::Rule> {
        self.outgoing_rules.values().flatten()
    }

    fn incoming_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule> {
        let o = self
            .outgoing_rules
            .values()
            .flatten()
            .filter(|r| r.target == *location)
            .collect::<HashSet<_>>();
        o.into_iter()
    }

    fn outgoing_rules(&self, location: &Location) -> impl Iterator<Item = &Self::Rule> {
        self.outgoing_rules.get(location).into_iter().flatten()
    }

    fn initial_location_constraints(&self) -> impl Iterator<Item = &LocationConstraint> {
        self.initial_location_constraint.iter()
    }

    fn initial_variable_constraints(&self) -> impl Iterator<Item = &BooleanVarConstraint> {
        self.initial_variable_constraint.iter()
    }

    fn has_decrements_or_resets(&self) -> bool {
        self.rules().any(|r| r.has_decrements() || r.has_resets())
    }

    fn has_decrements(&self) -> bool {
        self.rules().any(|r| r.has_decrements())
    }

    fn has_resets(&self) -> bool {
        self.rules().any(|r| r.has_resets())
    }
}

impl IsDeclared<Variable> for GeneralThresholdAutomaton {
    fn is_declared(&self, var: &Variable) -> bool {
        self.variables.contains(var)
    }
}

impl IsDeclared<Location> for GeneralThresholdAutomaton {
    fn is_declared(&self, loc: &Location) -> bool {
        self.locations.contains(loc)
    }
}

impl IsDeclared<Parameter> for GeneralThresholdAutomaton {
    fn is_declared(&self, param: &Parameter) -> bool {
        self.parameters.contains(param)
    }
}

// Here we decided to use the bymc format to display a threshold automaton,
// since it is well documented and easy to read.
impl Display for GeneralThresholdAutomaton {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ta_body = self.get_ta_body_in_bymc_format();

        write!(
            f,
            "thresholdAutomaton {} {{\n{}\n}}\n",
            self.name(),
            indent_all(ta_body)
        )
    }
}

impl PartialEq for GeneralThresholdAutomaton {
    fn eq(&self, other: &Self) -> bool {
        let self_out_rules = self
            .outgoing_rules
            .iter()
            .map(|(l, rs)| {
                let r_set = rs.iter().collect::<HashSet<_>>();
                (l, r_set)
            })
            .collect::<HashMap<_, HashSet<_>>>();
        let other_out_rules = other
            .outgoing_rules
            .iter()
            .map(|(l, rs)| {
                let r_set = rs.iter().collect::<HashSet<_>>();
                (l, r_set)
            })
            .collect::<HashMap<_, HashSet<_>>>();

        let self_init_loc = self
            .initial_location_constraint
            .iter()
            .collect::<HashSet<_>>();
        let other_init_loc = other
            .initial_location_constraint
            .iter()
            .collect::<HashSet<_>>();

        let self_init_var = self
            .initial_variable_constraint
            .iter()
            .collect::<HashSet<_>>();
        let other_init_var = other
            .initial_variable_constraint
            .iter()
            .collect::<HashSet<_>>();

        let self_rc = self.resilience_condition.iter().collect::<HashSet<_>>();
        let other_rc = other.resilience_condition.iter().collect::<HashSet<_>>();

        self.name == other.name
            && self.parameters == other.parameters
            && self.variables == other.variables
            && self.locations == other.locations
            && self_out_rules == other_out_rules
            && self_init_loc == other_init_loc
            && self_init_var == other_init_var
            && self_rc == other_rc
    }
}

/// Rule type for a [`GeneralThresholdAutomaton`]
///
/// This type represents the rules appearing in a [`GeneralThresholdAutomaton`].
#[derive(Debug, Eq, Clone, PartialOrd, Ord)]
pub struct Rule {
    /// Id assigned to the rule in the specification
    id: u32,
    /// Source location of the rule
    source: Location,
    /// Target location of the rule
    target: Location,
    /// Guards of the rule
    guard: BooleanVarConstraint,
    /// Effect of the rule
    actions: Vec<Action>,
}

impl Rule {
    /// Apply a transformation to the guard of the rule
    ///
    /// A transformation in this case is a function that mutates a
    /// [`BooleanVarConstraint`].
    pub fn transform_guard<F: FnMut(&mut BooleanVarConstraint)>(&mut self, mut t: F) {
        t(&mut self.guard);
    }

    /// Retains only the actions specified by the predicate.
    ///
    /// In other words, it will remove all elements e for which f(&e) returns
    /// false. This method operates in place, visiting each element exactly once
    /// in the original order, and preserves the order of the retained elements.
    pub fn retain_actions<F: Fn(&Action) -> bool>(&mut self, f: F) {
        self.actions.retain(f);
    }

    /// Updates the target location
    ///
    /// Needed for the Preprocessor CollapseLocations
    pub fn update_target(&mut self, loc: Location) {
        self.target = loc;
    }
}

impl RuleDefinition for Rule {
    type Action = Action;
    type Guard = BooleanVarConstraint;

    fn id(&self) -> u32 {
        self.id
    }

    fn source(&self) -> &Location {
        &self.source
    }

    fn target(&self) -> &Location {
        &self.target
    }

    fn guard(&self) -> &BooleanVarConstraint {
        &self.guard
    }

    fn actions(&self) -> impl Iterator<Item = &Self::Action> {
        self.actions.iter()
    }
}

impl Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let guard_string = self.guard.to_string();
        let update_string = join_iterator(self.actions.iter(), "; ");

        let rule_body = indent_all(format!("when ( {guard_string} )\ndo {{ {update_string} }}"));

        write!(
            f,
            "{}: {} -> {}\n{}",
            self.id, self.source, self.target, rule_body
        )
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Self) -> bool {
        let acts_self = self.actions.iter().collect::<HashSet<_>>();
        let acts_other = other.actions.iter().collect::<HashSet<_>>();

        self.id == other.id
            && self.source == other.source
            && self.target == other.target
            && self.guard == other.guard
            && acts_self == acts_other
    }
}

impl Hash for Rule {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.source.hash(state);
        self.target.hash(state);
        self.guard.hash(state);

        let acts = self.actions.iter().collect::<BTreeSet<_>>();
        acts.hash(state);
    }
}

/// Action on a shared variables
///
/// This struct defines action in a [`GeneralThresholdAutomaton`], describing
/// how executing a rule will update a shared variable.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct Action {
    /// Variable to be updated
    variable_to_update: Variable,
    /// Expression specifying the update rule
    update_expr: UpdateExpression,
}

/// Expressions defining an update to shared variables
///
/// This expression defines how a variable is updated. These expressions
/// are primarily used in [`Action`]s.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum UpdateExpression {
    /// Increment of variable
    Inc(u32),
    /// Decrement of variable
    Dec(u32),
    /// Value indicating that a variable is reset
    Reset,
    /// Unchanged variable
    Unchanged,
}

impl VariableConstraint for BooleanVarConstraint {
    fn as_boolean_expr(&self) -> BooleanExpression<Variable> {
        self.clone()
    }
}

impl Action {
    /// Get the update expression of the action
    pub fn update(&self) -> &UpdateExpression {
        &self.update_expr
    }
}

impl ActionDefinition for Action {
    fn variable(&self) -> &Variable {
        &self.variable_to_update
    }

    fn is_unchanged(&self) -> bool {
        match self.update_expr {
            UpdateExpression::Unchanged => true,
            UpdateExpression::Inc(_) | UpdateExpression::Dec(_) | UpdateExpression::Reset => false,
        }
    }

    fn is_reset(&self) -> bool {
        match self.update_expr {
            UpdateExpression::Reset => true,
            UpdateExpression::Inc(_) | UpdateExpression::Dec(_) | UpdateExpression::Unchanged => {
                false
            }
        }
    }

    fn is_increment(&self) -> bool {
        match &self.update_expr {
            UpdateExpression::Inc(_) => true,
            UpdateExpression::Reset | UpdateExpression::Dec(_) | UpdateExpression::Unchanged => {
                false
            }
        }
    }

    fn is_decrement(&self) -> bool {
        match &self.update_expr {
            UpdateExpression::Inc(_) | UpdateExpression::Reset | UpdateExpression::Unchanged => {
                false
            }
            UpdateExpression::Dec(_) => true,
        }
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.update_expr {
            UpdateExpression::Inc(_) | UpdateExpression::Dec(_) => {
                write!(
                    f,
                    "{}' == {} {}",
                    self.variable_to_update, self.variable_to_update, self.update_expr
                )
            }
            UpdateExpression::Reset => {
                write!(f, "{}' == {}", self.variable_to_update, self.update_expr)
            }
            UpdateExpression::Unchanged => write!(
                f,
                "{}' == {}",
                self.variable_to_update, self.variable_to_update
            ),
        }
    }
}

impl Display for UpdateExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UpdateExpression::Reset => write!(f, "0"),
            UpdateExpression::Inc(x) => write!(f, "+ {x}"),
            UpdateExpression::Dec(x) => write!(f, "- {x}"),
            UpdateExpression::Unchanged => write!(f, ""),
        }
    }
}

#[cfg(test)]
mod test {

    use crate::expressions::{ComparisonOp, IntegerExpression};
    use builder::{GeneralThresholdAutomatonBuilder, RuleBuilder};

    use super::*;
    use crate::expressions::{BooleanExpression, IntegerOp, Location, Parameter, Variable};
    use std::{collections::HashMap, vec};

    #[test]
    fn ta_has_decrements_or_resets() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_guard(BooleanExpression::True)
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(BooleanExpression::True)
                    .with_actions(vec![Action::new_reset(Variable::new("var1"))])
                    .build(),
            ])
            .unwrap()
            .build();

        assert!(ta.has_decrements_or_resets());
        assert!(!ta.has_decrements());
        assert!(ta.has_resets());

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_guard(BooleanExpression::True)
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(BooleanExpression::True)
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1"))
                                - IntegerExpression::Const(1),
                        )
                        .unwrap(),
                    ])
                    .build(),
            ])
            .unwrap()
            .build();
        assert!(ta.has_decrements_or_resets());

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_guard(BooleanExpression::True)
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(BooleanExpression::True)
                    .with_actions(vec![
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Const(1)
                                + IntegerExpression::Atom(Variable::new("var1")),
                        )
                        .unwrap(),
                    ])
                    .build(),
            ])
            .unwrap()
            .build();
        assert!(!ta.has_decrements_or_resets());
        assert!(!ta.has_decrements());
        assert!(!ta.has_resets());
    }

    #[test]
    fn test_ta_getters() {
        let ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ]),
            initial_variable_constraint: vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )],
            outgoing_rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![Rule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![Rule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                        actions: vec![
                            Action {
                                variable_to_update: Variable::new("var3"),
                                update_expr: UpdateExpression::Reset,
                            },
                            Action {
                                variable_to_update: Variable::new("var1"),
                                update_expr: UpdateExpression::Inc(1),
                            },
                        ],
                    }],
                ),
            ]),

            initial_location_constraint: vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ],
            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )],
        };

        assert_eq!(ta.name(), "test_ta1");

        assert!(
            [
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3")
            ]
            .iter()
            .all(|loc| ta.locations().any(|ta_l| ta_l == loc))
        );

        assert!(
            [
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3")
            ]
            .iter()
            .all(|var| ta.variables().any(|ta_v| ta_v == var))
        );

        assert!(
            [
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f")
            ]
            .iter()
            .all(|param| ta.parameters().any(|ta_p| ta_p == param))
        );

        assert!(
            [BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )]
            .iter()
            .all(|var_constr| ta
                .initial_variable_conditions()
                .any(|ta_vc| ta_vc == var_constr))
        );

        assert!(
            [LocationConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(
                    IntegerExpression::Param(Parameter::new("n"))
                        - IntegerExpression::Param(Parameter::new("f")),
                ),
            ) | LocationConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )]
            .iter()
            .all(|loc_constr| ta
                .initial_location_conditions()
                .any(|ta_lc| ta_lc == loc_constr))
        );

        assert!(
            [ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )]
            .iter()
            .all(|param_constr| ta
                .resilience_conditions()
                .any(|ta_rc| ta_rc == param_constr))
        );

        assert!(
            [
                Rule {
                    id: 0,
                    source: Location::new("loc1"),
                    target: Location::new("loc2"),
                    guard: BooleanExpression::True,
                    actions: vec![],
                },
                Rule {
                    id: 1,
                    source: Location::new("loc2"),
                    target: Location::new("loc3"),
                    guard: BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ) & BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ),
                    actions: vec![
                        Action {
                            variable_to_update: Variable::new("var3"),
                            update_expr: UpdateExpression::Reset,
                        },
                        Action {
                            variable_to_update: Variable::new("var1"),
                            update_expr: UpdateExpression::Inc(1),
                        },
                    ],
                }
            ]
            .iter()
            .all(|rule| ta.rules().any(|ta_r| ta_r == rule))
        );

        assert_eq!(ta.outgoing_rules(&Location::new("loc1")).count(), 1);
        assert!(ta.outgoing_rules(&Location::new("loc1")).any(|r| *r
            == Rule {
                id: 0,
                source: Location::new("loc1"),
                target: Location::new("loc2"),
                guard: BooleanExpression::True,
                actions: vec![],
            }));

        assert_eq!(ta.resilience_conditions().count(), 1);
        assert!(ta.resilience_conditions().any(|r| *r
            == ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )));

        assert_eq!(ta.incoming_rules(&Location::new("loc2")).count(), 1);
        assert!(ta.incoming_rules(&Location::new("loc2")).any(|r| *r
            == Rule {
                id: 0,
                source: Location::new("loc1"),
                target: Location::new("loc2"),
                guard: BooleanExpression::True,
                actions: vec![],
            }));

        assert!(ta.is_declared(&Variable::new("var1")));
        assert!(ta.is_declared(&Variable::new("var2")));
        assert!(ta.is_declared(&Variable::new("var3")));
    }

    #[test]
    fn test_ta_remove_rule() {
        let mut ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ]),
            initial_variable_constraint: vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )],
            outgoing_rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![Rule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![Rule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                        actions: vec![
                            Action {
                                variable_to_update: Variable::new("var3"),
                                update_expr: UpdateExpression::Reset,
                            },
                            Action {
                                variable_to_update: Variable::new("var1"),
                                update_expr: UpdateExpression::Inc(1),
                            },
                        ],
                    }],
                ),
                (
                    Location::new("loc3"),
                    vec![Rule {
                        id: 3,
                        source: Location::new("loc3"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
            ]),

            initial_location_constraint: vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ],
            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )],
        };

        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        ta.retain_rules(|r| *r != rule);

        let expected_ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ]),
            initial_variable_constraint: vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )],
            outgoing_rules: HashMap::from([
                (
                    Location::new("loc2"),
                    vec![Rule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                        actions: vec![
                            Action {
                                variable_to_update: Variable::new("var3"),
                                update_expr: UpdateExpression::Reset,
                            },
                            Action {
                                variable_to_update: Variable::new("var1"),
                                update_expr: UpdateExpression::Inc(1),
                            },
                        ],
                    }],
                ),
                (
                    Location::new("loc3"),
                    vec![Rule {
                        id: 3,
                        source: Location::new("loc3"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
            ]),

            initial_location_constraint: vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ],
            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )],
        };

        assert_eq!(ta, expected_ta);
    }

    #[test]
    fn test_ta_remove_location() {
        let mut ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ]),
            initial_variable_constraint: vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )],
            outgoing_rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![Rule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![Rule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                        actions: vec![
                            Action {
                                variable_to_update: Variable::new("var3"),
                                update_expr: UpdateExpression::Reset,
                            },
                            Action {
                                variable_to_update: Variable::new("var1"),
                                update_expr: UpdateExpression::Inc(1),
                            },
                        ],
                    }],
                ),
                (
                    Location::new("loc3"),
                    vec![Rule {
                        id: 3,
                        source: Location::new("loc3"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![],
                    }],
                ),
            ]),

            initial_location_constraint: vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ],
            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )],
        };

        ta.remove_location_and_replace_with(&Location::new("loc3"), IntegerExpression::Const(0));

        let expected_ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([Location::new("loc1"), Location::new("loc2")]),
            initial_variable_constraint: vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )],
            outgoing_rules: HashMap::from([(
                Location::new("loc1"),
                vec![Rule {
                    id: 0,
                    source: Location::new("loc1"),
                    target: Location::new("loc2"),
                    guard: BooleanExpression::True,
                    actions: vec![],
                }],
            )]),

            initial_location_constraint: vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ],
            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )],
        };

        assert_eq!(ta, expected_ta,);
    }

    #[test]
    fn test_can_be_initial_location() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
                Location::new("loc4"),
                Location::new("loc5"),
                Location::new("loc6"),
            ])
            .unwrap()
            .initialize()
            .with_initial_location_constraints(vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1) + -IntegerExpression::Const(1)),
                ),
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc4"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1) * IntegerExpression::Const(0)),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc4"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc5"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ) & LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc5"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                ),
                LocationConstraint::True,
                LocationConstraint::False,
                !LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc6"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Const(0)),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        assert!(!ta.can_be_initial_location(&Location::new("loc1")));
        assert!(!ta.can_be_initial_location(&Location::new("loc2")));
        assert!(ta.can_be_initial_location(&Location::new("loc3")));
        assert!(!ta.can_be_initial_location(&Location::new("loc4")));
        assert!(!ta.can_be_initial_location(&Location::new("loc5")));
        assert!(ta.can_be_initial_location(&Location::new("loc6")));
    }

    #[test]
    fn test_display_ta() {
        let ta = GeneralThresholdAutomaton {
            name: "test_ta1".to_string(),
            parameters: HashSet::from([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ]),
            variables: HashSet::from([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ]),
            locations: HashSet::from([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ]),
            initial_variable_constraint: vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )],
            outgoing_rules: HashMap::from([
                (
                    Location::new("loc1"),
                    vec![Rule {
                        id: 0,
                        source: Location::new("loc1"),
                        target: Location::new("loc2"),
                        guard: BooleanExpression::True,
                        actions: vec![
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::Atom(Variable::new("var1")),
                            )
                            .unwrap(),
                        ],
                    }],
                ),
                (
                    Location::new("loc2"),
                    vec![Rule {
                        id: 1,
                        source: Location::new("loc2"),
                        target: Location::new("loc3"),
                        guard: BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                        actions: vec![
                            Action {
                                variable_to_update: Variable::new("var3"),
                                update_expr: UpdateExpression::Reset,
                            },
                            Action {
                                variable_to_update: Variable::new("var1"),
                                update_expr: UpdateExpression::Inc(1),
                            },
                        ],
                    }],
                ),
            ]),

            initial_location_constraint: vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ],

            resilience_condition: vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )],
        };
        let expected_ta_string = "thresholdAutomaton test_ta1 {
    shared var1, var2, var3;

    parameters f, n, t;

    assumptions (1) {
        n > (3 * f);
    }

    locations (3) {
        loc1:[0];
        loc2:[1];
        loc3:[2];
    }

    inits (2) {
        (loc1 == (n - f) || loc2 == 0);
        var1 == 1;
    }

    rules (2) {
        0: loc1 -> loc2
            when ( true )
            do { var1' == var1 };
        1: loc2 -> loc3
            when ( (var1 == 1 && var2 == n) )
            do { var3' == 0; var1' == var1 + 1 };
    }
}
";

        assert_eq!(ta.to_bymc(), expected_ta_string);
        assert_eq!(ta.to_string(), expected_ta_string);
    }

    #[test]
    fn test_rule_getters() {
        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        assert_eq!(rule.id(), 0);
        assert_eq!(rule.source(), &Location::new("loc1"));
        assert_eq!(rule.target(), &Location::new("loc2"));
        assert_eq!(rule.guard(), &BooleanExpression::True);
        assert_eq!(rule.actions().cloned().collect::<Vec<Action>>(), vec![]);

        assert_eq!(rule.guard().as_boolean_expr(), BooleanExpression::True);
    }

    #[test]
    fn test_rule_has_decrements_or_resets() {
        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![],
        };
        assert!(!rule.has_resets());
        assert!(!rule.has_decrements());

        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![Action::new_reset(Variable::new("var1"))],
        };
        assert!(rule.has_resets());
        assert!(!rule.has_decrements());

        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::Atom(Variable::new("var1")) - IntegerExpression::Const(1),
                )
                .unwrap(),
            ],
        };
        assert!(!rule.has_resets());
        assert!(rule.has_decrements());

        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::Const(1) + IntegerExpression::Atom(Variable::new("var1")),
                )
                .unwrap(),
                Action::new(
                    Variable::new("var2"),
                    IntegerExpression::Const(1) + IntegerExpression::Atom(Variable::new("var2")),
                )
                .unwrap(),
            ],
        };
        assert!(!rule.has_resets());
        assert!(!rule.has_decrements());

        let rule = Rule {
            id: 0,
            source: Location::new("loc1"),
            target: Location::new("loc2"),
            guard: BooleanExpression::True,
            actions: vec![
                Action::new_reset(Variable::new("var1")),
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::Atom(Variable::new("var1")) - IntegerExpression::Const(1),
                )
                .unwrap(),
            ],
        };
        assert!(rule.has_resets());
        assert!(rule.has_decrements());
    }

    #[test]
    fn test_action_getters() {
        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Inc(1),
        };

        assert_eq!(act.variable(), &Variable::new("var1"));
        assert_eq!(act.update(), &UpdateExpression::Inc(1));
    }

    #[test]
    fn test_action_is_reset() {
        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Reset,
        };
        assert!(act.is_reset());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Inc(1),
        };
        assert!(!act.is_reset());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Dec(1),
        };
        assert!(!act.is_reset());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Unchanged,
        };
        assert!(!act.is_reset());

        let act = Action::new_reset(Variable::new("var1"));
        assert!(act.is_reset());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Const(1) + IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(!act.is_reset());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Const(5) + -IntegerExpression::Const(5),
        )
        .unwrap();
        assert!(act.is_reset());
    }

    #[test]
    fn test_act_is_decrement() {
        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Dec(1),
        };
        assert!(act.is_decrement());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Inc(1),
        };
        assert!(!act.is_decrement());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Reset,
        };
        assert!(!act.is_decrement());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Unchanged,
        };
        assert!(!act.is_decrement());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Atom(Variable::new("var1")) - IntegerExpression::Const(1),
        )
        .unwrap();
        assert!(act.is_decrement());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Const(1) + IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(!act.is_decrement());

        let act = Action::new(
            Variable::new("var1"),
            -IntegerExpression::Const(5) + IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(act.is_decrement());
    }

    #[test]
    fn test_act_is_unchanged() {
        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Unchanged,
        };
        assert!(act.is_unchanged());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Inc(1),
        };
        assert!(!act.is_unchanged());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Dec(1),
        };
        assert!(!act.is_unchanged());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Reset,
        };
        assert!(!act.is_unchanged());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(act.is_unchanged());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Const(1) + IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(!act.is_unchanged());

        let act = Action::new(
            Variable::new("var1"),
            -IntegerExpression::Const(5) + IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(!act.is_unchanged());
    }

    #[test]
    fn test_act_is_increment() {
        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Inc(1),
        };
        assert!(act.is_increment());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Dec(1),
        };
        assert!(!act.is_increment());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Reset,
        };
        assert!(!act.is_increment());

        let act = Action {
            variable_to_update: Variable::new("var1"),
            update_expr: UpdateExpression::Unchanged,
        };
        assert!(!act.is_increment());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Const(1) + IntegerExpression::Atom(Variable::new("var1")),
        )
        .unwrap();
        assert!(act.is_increment());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Atom(Variable::new("var1")) - IntegerExpression::Const(1),
        )
        .unwrap();
        assert!(!act.is_increment());

        let act = Action::new(
            Variable::new("var1"),
            IntegerExpression::Atom(Variable::new("var1")) + IntegerExpression::Const(5),
        )
        .unwrap();
        assert!(act.is_increment());
    }

    #[test]
    fn test_update_expr_display() {
        let inc_expr = UpdateExpression::Inc(1);
        let dec_expr = UpdateExpression::Dec(1);
        let reset_expr = UpdateExpression::Reset;
        let unchanged_expr = UpdateExpression::Unchanged;

        assert_eq!(inc_expr.to_string(), "+ 1");
        assert_eq!(dec_expr.to_string(), "- 1");
        assert_eq!(reset_expr.to_string(), "0");
        assert_eq!(unchanged_expr.to_string(), "");
    }

    #[test]
    fn test_set_name() {
        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .initialize()
            .build();
        ta.set_name("new_ta".to_string());

        assert_eq!(ta.name(), "new_ta")
    }

    #[test]
    fn test_add_rule() {
        let r = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![Location::new("loc1"), Location::new("loc2")])
            .unwrap()
            .initialize()
            .with_initial_location_constraints(vec![])
            .unwrap()
            .build();

        ta.add_rule(r);

        assert!(ta.outgoing_rules.contains_key(&Location::new("loc1")));
        assert!(
            ta.outgoing_rules[&Location::new("loc1")]
                .iter()
                .any(|rule| rule.id == 0)
        );
    }

    #[test]
    fn test_add_resilience_condition() {
        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![Location::new("loc1"), Location::new("loc2")])
            .unwrap()
            .with_parameters(vec![
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ])
            .unwrap()
            .initialize()
            .with_initial_location_constraints(vec![])
            .unwrap()
            .build();

        let condition = ParameterConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(0)),
        );

        ta.add_resilience_conditions([condition.clone()]);

        assert_eq!(ta.resilience_condition.len(), 1);
        assert_eq!(ta.resilience_condition[0], condition);
    }

    #[test]
    fn test_add_initial_location_constraint() {
        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![Location::new("loc1"), Location::new("loc2")])
            .unwrap()
            .initialize()
            .with_initial_location_constraints(vec![])
            .unwrap()
            .build();

        let constraint = LocationConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        ta.add_initial_location_constraints([constraint.clone()]);

        assert_eq!(ta.initial_location_constraint.len(), 1);
        assert_eq!(ta.initial_location_constraint[0], constraint);
    }

    #[test]
    fn test_add_initial_variable_constraint() {
        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![Location::new("loc1"), Location::new("loc2")])
            .unwrap()
            .with_variables(vec![
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .with_initial_variable_constraints(vec![])
            .unwrap()
            .build();

        let constraint = BooleanVarConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        ta.add_initial_variable_constraints([constraint.clone()]);

        assert_eq!(ta.initial_variable_constraint.len(), 1);
        assert_eq!(ta.initial_variable_constraint[0], constraint);
    }

    #[test]
    fn test_retain_rule() {
        let r0 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let r1 = Rule {
            id: 1,
            source: Location::new("loc2"),
            target: Location::new("loc1"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![Location::new("loc1"), Location::new("loc2")])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone()])
            .unwrap()
            .build();

        ta.retain_rules(|rule| *rule != r0);

        assert_eq!(ta.rules().count(), 1);
        assert!(!ta.rules().any(|r| *r == r0));
        assert!(ta.rules().any(|r| *r == r1));
    }

    #[test]
    fn test_transform_rules() {
        let r0 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let r1 = Rule {
            id: 1,
            source: Location::new("loc2"),
            target: Location::new("loc1"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
                Location::new("loc4"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone()])
            .unwrap()
            .build();

        ta.transform_rules(|rule| {
            if rule.id == 0 {
                rule.source = Location::new("loc3");
                rule.target = Location::new("loc4");
                rule.id = 2;
            }
        });

        let r2 = Rule {
            id: 2,
            source: Location::new("loc3"),
            target: Location::new("loc4"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        assert_eq!(ta.rules().count(), 2);
        assert!(ta.rules().any(|r| *r == r1));
        assert!(ta.rules().any(|r| *r == r2));
        assert!(!ta.rules().any(|r| *r == r0));
    }

    #[test]
    fn test_remove_location() {
        let r0 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::True)
            .build();

        let r1 = Rule {
            id: 1,
            source: Location::new("loc3"),
            target: Location::new("loc4"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        let r2 = Rule {
            id: 2,
            source: Location::new("loc4"),
            target: Location::new("loc3"),
            guard: BooleanExpression::True,
            actions: vec![],
        };

        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
                Location::new("loc4"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone(), r2.clone()])
            .unwrap()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .unwrap()
            .build();

        ta.remove_location_and_replace_with(&Location::new("loc3"), IntegerExpression::Const(0));

        assert_eq!(ta.locations().count(), 3);
        assert!(!ta.locations().any(|l| *l == Location::new("loc3")));

        assert_eq!(ta.rules().count(), 1);
        assert!(ta.rules().any(|r| *r == r0));
        assert!(!ta.rules().any(|r| *r == r1));
        assert!(!ta.rules().any(|r| *r == r2));

        let expected_cond = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(0)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        assert_eq!(ta.initial_location_conditions().count(), 1);
        assert!(
            ta.initial_location_conditions()
                .any(|c| *c == expected_cond)
        );
    }

    #[test]
    fn test_remove_variable() {
        let r0 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();

        let r1 = Rule {
            id: 1,
            source: Location::new("loc3"),
            target: Location::new("loc4"),
            guard: BooleanExpression::True,
            actions: vec![
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::Atom(Variable::new("var1")) + IntegerExpression::Const(1),
                )
                .unwrap(),
                Action::new(
                    Variable::new("var2"),
                    IntegerExpression::Atom(Variable::new("var2")) + IntegerExpression::Const(1),
                )
                .unwrap(),
            ],
        };

        let mut ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
                Location::new("loc4"),
            ])
            .unwrap()
            .with_variables(vec![
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r0.clone(), r1.clone()])
            .unwrap()
            .with_initial_variable_constraints([BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )])
            .unwrap()
            .build();

        ta.remove_variable_and_replace_with(&Variable::new("var1"), IntegerExpression::Const(0));

        assert_eq!(ta.variables().count(), 2);
        assert!(!ta.variables().any(|v| *v == Variable::new("var1")));

        let expected_r0 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Const(0)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .build();
        let expected_r1 = Rule {
            id: 1,
            source: Location::new("loc3"),
            target: Location::new("loc4"),
            guard: BooleanExpression::True,
            actions: vec![
                Action::new(
                    Variable::new("var2"),
                    IntegerExpression::Atom(Variable::new("var2")) + IntegerExpression::Const(1),
                )
                .unwrap(),
            ],
        };

        assert_eq!(ta.rules().count(), 2);
        assert!(ta.rules().any(|r| *r == expected_r0));
        assert!(ta.rules().any(|r| *r == expected_r1));

        assert_eq!(ta.initial_variable_constraints().count(), 1);
        assert!(ta.initial_variable_constraints().any(|c| *c
            == BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Const(0)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )));
    }
}

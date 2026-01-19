//! Reachability specification for model checkers
//!
//! This module defines the types for reachability specifications in threshold
//! automata. On a high-level, a reachability specification asks whether an
//! upwards closed set of locations can be reached.
//!
//! In more detail, a reachability consists of two parts:
//! - A constraint that narrows down the set of initial locations (we will also
//!   name this part of the specification `init`).
//! - A constraint specifying the set of configurations that should be
//!   reached (we will also call this part of the constraint `target`).
//!
//! Such a constraint can be seen as an (E)LTL formula:
//!     `(init) => <>(target)`
//!
//! This module contains the logic to transform an arbitrary ELTL constraint
//! into a constraint of that form, assuming that it is a safety constraint
//! (i.e., it does not contain a `[]`).
//!
//! A reachability specification allows to specify a set of locations
//! with a number of processes that must be **at least** in that location, as
//! well as a set of locations that should not contain any processes.
//! Additionally, one can specify a constraint on the valuations of the shared
//! variables.

use std::{
    collections::{HashMap, HashSet},
    error,
    fmt::{self},
    ops::Not,
};

use log::{debug, error, warn};
use taco_display_utils::join_iterator;
use taco_smt_encoder::expression_encoding::{EncodeToSMT, SMTSolverError, SMTVariableContext};
use taco_threshold_automaton::{
    ModifiableThresholdAutomaton, VariableConstraint,
    expressions::{
        BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        fraction::Fraction,
    },
    lia_threshold_automaton::{
        ConstraintRewriteError, LIAVariableConstraint, integer_thresholds::Threshold,
    },
};

use crate::{
    ModelCheckerContext, SpecificationTrait, TargetSpec,
    eltl::{ELTLExpression, remove_negations::NonNegatedELTLExpression},
};

/// A named reachability Property
#[derive(Clone, Debug, PartialEq)]
pub struct ReachabilityProperty {
    /// Name of the property
    name: String,
    /// Disjunctions over constraints of the form (_) && <>(_)
    disj: Vec<Reachability>,
}

impl ReachabilityProperty {
    /// Try to construct a new reachability property from an ELTLExpression
    pub fn from_named_eltl<S: ToString>(
        name: S,
        expr: ELTLExpression,
    ) -> Result<Self, ReachabilityTransformationError> {
        let name = name.to_string();
        let disj = Reachability::try_from_eltl(name.clone(), expr.not().into())?;

        Ok(Self { name, disj })
    }

    /// Check whether this constraint contains a reachability constraint
    ///
    /// A reachability constraint requires at least one location to be empty.
    pub fn contains_reachability_constraint(&self) -> bool {
        self.disj
            .iter()
            .any(|c| c.contains_reachability_constraint())
    }

    /// Create the threshold automata that need to be checked
    pub fn create_tas_to_check<T: ModifiableThresholdAutomaton>(
        &self,
        ta: &T,
    ) -> impl Iterator<Item = (DisjunctionTargetConfig, T)> {
        self.clone().disj.into_iter().map(move |reach| {
            let mut ta = ta.clone();

            ta.set_name(ta.name().to_string() + "-" + reach.target.name());

            ta.add_initial_location_constraints(reach.precondition_loc);
            ta.add_initial_variable_constraints(reach.precondition_var);
            ta.add_resilience_conditions(reach.precondition_par);

            (reach.target, ta)
        })
    }

    /// Get the name of the specification
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Create a new property
    pub fn new<S: Into<String>, T: Into<Reachability>>(name: S, targets: T) -> Self {
        let spec = targets.into();
        Self {
            name: name.into(),
            disj: vec![spec],
        }
    }
}

impl<C: ModelCheckerContext> SpecificationTrait<C> for ReachabilityProperty {
    type TransformationError = ReachabilityTransformationError;

    fn try_from_eltl(
        spec: impl Iterator<Item = (String, crate::eltl::ELTLExpression)>,
        _ctx: &C,
    ) -> Result<Vec<Self>, Self::TransformationError> {
        let mut res_properties = Vec::new();

        for (name, expr) in spec {
            let res = Self::from_named_eltl(name.clone(), expr.clone());
            if let Err(ReachabilityTransformationError::LivenessSpecification) = res {
                warn!(
                    "Specification '{name}' is a liveness specification, which are currently not supported by TACO. Skipping ..."
                );
                debug!("Classified property '{name}' as liveness. Expression: {expr}");
                continue;
            }

            let res = res?;
            res_properties.push(res);
        }

        Ok(res_properties)
    }

    type InternalSpecType = DisjunctionTargetConfig;

    fn transform_threshold_automaton<
        TA: taco_threshold_automaton::ThresholdAutomaton + ModifiableThresholdAutomaton,
    >(
        ta: TA,
        specs: Vec<Self>,
        _ctx: &C,
    ) -> Vec<(Self::InternalSpecType, TA)> {
        specs
            .into_iter()
            .flat_map(|spec| spec.create_tas_to_check(&ta).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    }
}

/// Formula of the form `(preconditions) => <>(target)`
///
/// A reachability constraint specifies
/// - a set of starting configurations
/// - a set of target configurations
///
/// The set of starting configurations is a subset of the threshold automaton.
/// This type allows these restriction to be arbitrary boolean conditions on
/// parameters, variables and locations (mostly since they appear in benchmarks
/// of the ByMC tool).
///
/// Target constraints are more restricted. We only allow for lower bounds on
/// the number of processes, or specifying that a location should not be
/// covered. These constraints match the formal definition of ELTL formulas in
/// the related literature (e.g., see paper
/// ["A Short Counterexample Property for Safety and Liveness Verification of Fault-Tolerant Distributed Algorithms"](https://arxiv.org/abs/1608.05327)
/// by Konnov et al.).
/// Other constraints, such as upper bounds, can be seen as pathological and
/// decision procedures may be incomplete for these specifications.
///
///
/// To handle these conditions, add them to the initial constraints of the
/// threshold automaton, preferably before transforming the automaton in a
/// necessary intermediate format.
#[derive(Debug, Clone, PartialEq)]
pub struct Reachability {
    /// Conjunction of conditions on the parameter evaluation
    precondition_par: Vec<BooleanExpression<Parameter>>,
    /// Conjunction of conditions on the initial distribution of processes in the threshold
    /// automaton
    precondition_loc: Vec<BooleanExpression<Location>>,
    /// Conjunction of conditions on the initial valuation of the shared variables
    precondition_var: Vec<BooleanExpression<Variable>>,
    /// Conditions on the configuration to reach
    target: DisjunctionTargetConfig,
}

impl And for Reachability {
    fn and(mut self, other: Reachability) -> Self {
        self.precondition_par.reserve(other.precondition_par.len());
        self.precondition_par.extend(other.precondition_par);

        self.precondition_loc.reserve(other.precondition_loc.len());
        self.precondition_loc.extend(other.precondition_loc);

        self.precondition_var.reserve(other.precondition_var.len());
        self.precondition_var.extend(other.precondition_var);

        self.target = self.target.and(other.target);

        self
    }
}

impl Reachability {
    /// Create a new reachability constraint that has no constraints
    fn new_unconstrained(name: String) -> Self {
        Reachability {
            precondition_par: vec![],
            precondition_loc: vec![],
            precondition_var: vec![],
            target: DisjunctionTargetConfig::new_empty(name),
        }
    }

    /// Create a new reachability constraint with only a single parameter
    /// constraint
    fn new_with_parameter_constr(
        name: String,
        lhs: Box<IntegerExpression<Parameter>>,
        op: ComparisonOp,
        rhs: Box<IntegerExpression<Parameter>>,
    ) -> Self {
        Reachability {
            precondition_par: vec![BooleanExpression::ComparisonExpression(lhs, op, rhs)],
            precondition_loc: vec![],
            precondition_var: vec![],
            target: DisjunctionTargetConfig::new_empty(name),
        }
    }

    /// Create a new reachability constraint with only a single initial location
    /// constraint
    fn new_with_initial_loc_constr(
        name: String,
        lhs: Box<IntegerExpression<Location>>,
        op: ComparisonOp,
        rhs: Box<IntegerExpression<Location>>,
    ) -> Self {
        Reachability {
            precondition_par: vec![],
            precondition_loc: vec![BooleanExpression::ComparisonExpression(lhs, op, rhs)],
            precondition_var: vec![],
            target: DisjunctionTargetConfig::new_empty(name),
        }
    }

    /// Create a new reachability constraint with only a single initial variable
    /// constraint
    fn new_with_initial_var_constr(
        name: String,
        lhs: Box<IntegerExpression<Variable>>,
        op: ComparisonOp,
        rhs: Box<IntegerExpression<Variable>>,
    ) -> Self {
        Reachability {
            precondition_par: vec![],
            precondition_loc: vec![],
            precondition_var: vec![BooleanExpression::ComparisonExpression(lhs, op, rhs)],
            target: DisjunctionTargetConfig::new_empty(name),
        }
    }

    /// Create a new reachability constraint with only an eventual constraint
    fn new_with_eventual_reach(disj: DisjunctionTargetConfig) -> Self {
        Reachability {
            precondition_par: vec![],
            precondition_loc: vec![],
            precondition_var: vec![],
            target: disj,
        }
    }

    /// Check whether this constraint contains a reachability constraint
    ///
    /// A reachability constraint requires at least one location to be empty.
    pub fn contains_reachability_constraint(&self) -> bool {
        self.target.contains_reachability_constraint()
    }

    /// Get the target specification of the reachability specification
    ///
    /// A [`Reachability`] object is a specification of the form
    /// `(preconditions) => <>(target)`
    /// This function returns the target as a [`DisjunctionTargetConfig`]
    pub fn get_target_conditions(&self) -> &DisjunctionTargetConfig {
        &self.target
    }

    /// Try to construct a reachability constraint from a an ELTL formula
    fn try_from_eltl(
        name: String,
        spec: NonNegatedELTLExpression,
    ) -> Result<Vec<Self>, ReachabilityTransformationError> {
        match spec {
            NonNegatedELTLExpression::Globally(_expr) => {
                Err(ReachabilityTransformationError::LivenessSpecification)
            }
            NonNegatedELTLExpression::Eventually(expr) => {
                let inner = Self::parse_in_eventually(name, *expr)?;
                Ok(vec![Self::new_with_eventual_reach(inner)])
            }
            NonNegatedELTLExpression::And(lhs, rhs) => {
                let lhs = Self::try_from_eltl(name.clone(), *lhs)?;
                let rhs = Self::try_from_eltl(name, *rhs)?;

                let mut new_constrs = Vec::with_capacity(lhs.len() * rhs.len());
                for constr in &lhs {
                    for o_constr in &rhs {
                        new_constrs.push(constr.clone().and(o_constr.clone()));
                    }
                }

                Ok(new_constrs)
            }
            NonNegatedELTLExpression::Or(lhs, rhs) => {
                let mut lhs = Reachability::try_from_eltl(name.clone(), *lhs)?;
                let mut rhs = Reachability::try_from_eltl(name, *rhs)?;

                lhs.reserve(rhs.len());
                lhs.append(&mut rhs);
                Ok(lhs)
            }
            NonNegatedELTLExpression::LocationExpr(lhs, op, rhs) => {
                Ok(vec![Self::new_with_initial_loc_constr(name, lhs, op, rhs)])
            }
            NonNegatedELTLExpression::VariableExpr(lhs, op, rhs) => {
                Ok(vec![Self::new_with_initial_var_constr(name, lhs, op, rhs)])
            }
            NonNegatedELTLExpression::ParameterExpr(lhs, op, rhs) => {
                Ok(vec![Self::new_with_parameter_constr(name, lhs, op, rhs)])
            }
            NonNegatedELTLExpression::True => Ok(vec![Self::new_unconstrained(name)]),
            NonNegatedELTLExpression::False => Ok(vec![]),
        }
    }

    /// Try to parse the constraints behind an eventually operator into a
    /// disjunction of upwards closed sets
    fn parse_in_eventually(
        name: String,
        expr: NonNegatedELTLExpression,
    ) -> Result<DisjunctionTargetConfig, ReachabilityTransformationError> {
        match expr {
            NonNegatedELTLExpression::Eventually(expr) => Self::parse_in_eventually(name, *expr),
            NonNegatedELTLExpression::Or(lhs, rhs) => {
                let lhs = Self::parse_in_eventually(name.clone(), *lhs)?;
                let rhs = Self::parse_in_eventually(name, *rhs)?;

                Ok(lhs.or(rhs))
            }
            NonNegatedELTLExpression::And(lhs, rhs) => {
                let lhs = Self::parse_in_eventually(name.clone(), *lhs)?;
                let rhs = Self::parse_in_eventually(name, *rhs)?;

                Ok(lhs.and(rhs))
            }
            NonNegatedELTLExpression::LocationExpr(lhs, op, rhs) => {
                let reach = TargetConfig::try_from_loc_constr((*lhs, op, *rhs))?;

                Ok(DisjunctionTargetConfig::new_with_single_disjunct(
                    name, reach,
                ))
            }
            NonNegatedELTLExpression::VariableExpr(lhs, op, rhs) => {
                let var = BooleanExpression::ComparisonExpression(lhs, op, rhs);
                let loc = TargetConfig::new_with_var_constr(var)?;

                Ok(DisjunctionTargetConfig::new_with_single_disjunct(name, loc))
            }
            NonNegatedELTLExpression::True => {
                Ok(DisjunctionTargetConfig::new_with_single_disjunct(
                    name,
                    TargetConfig::new_unconstrained(),
                ))
            }
            NonNegatedELTLExpression::False => Ok(DisjunctionTargetConfig::new_empty(name)),
            NonNegatedELTLExpression::Globally(_expr) => {
                Err(ReachabilityTransformationError::LivenessSpecification)
            }
            NonNegatedELTLExpression::ParameterExpr(_, _, _) => unreachable!(
                "This case should have been filtered out when validating the specification"
            ),
        }
    }
}

impl<D: Into<DisjunctionTargetConfig>> From<D> for Reachability {
    fn from(value: D) -> Self {
        let disj = value.into();
        Reachability::new_with_eventual_reach(disj)
    }
}

/// Disjunction over multiple target configurations
///
/// This type represents a disjunction of [`TargetConfig`]
#[derive(Debug, Clone, PartialEq)]
pub struct DisjunctionTargetConfig {
    /// Name of the property this specification has been derived from
    property_name: String,
    /// Sets of target configurations
    targets: Vec<TargetConfig>,
}

impl fmt::Display for DisjunctionTargetConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", join_iterator(self.targets.iter(), " || "))
    }
}

impl Or for DisjunctionTargetConfig {
    fn or(mut self, other: Self) -> Self {
        self.targets.reserve(other.targets.len());
        self.targets.extend(other.targets);
        self
    }
}

impl And for DisjunctionTargetConfig {
    fn and(self, other: DisjunctionTargetConfig) -> DisjunctionTargetConfig {
        if self.targets.is_empty() {
            return other;
        }

        if other.targets.is_empty() {
            return self;
        }

        let mut constrs = Vec::with_capacity(self.targets.len() * other.targets.len());

        for constr in self.targets {
            for o_constr in other.targets.iter() {
                constrs.push(constr.clone().and(o_constr.clone()));
            }
        }

        debug_assert!(
            self.property_name == other.property_name,
            "Combined target configurations from different properties"
        );

        Self {
            property_name: self.property_name,
            targets: constrs,
        }
    }
}

impl TargetSpec for DisjunctionTargetConfig {
    fn get_locations_in_target(&self) -> impl IntoIterator<Item = &Location> {
        self.get_locations_appearing()
    }

    fn get_variable_constraint(
        &self,
    ) -> impl IntoIterator<
        Item = &taco_threshold_automaton::lia_threshold_automaton::LIAVariableConstraint,
    > {
        self.targets.iter().map(|t| t.get_variable_constraint())
    }
}

impl DisjunctionTargetConfig {
    /// Create a new disjunction without any disjuncts
    fn new_empty(name: String) -> Self {
        Self {
            property_name: name,
            targets: Vec::new(),
        }
    }

    /// Create a disjunction only containing a single disjunct
    fn new_with_single_disjunct(name: String, u: TargetConfig) -> Self {
        Self {
            property_name: name,
            targets: vec![u],
        }
    }

    /// Create a disjunction from the given disjuncts
    pub fn new_from_targets<I: IntoIterator<Item = TargetConfig>>(name: String, disj: I) -> Self {
        Self {
            property_name: name,
            targets: disj.into_iter().collect(),
        }
    }

    /// Check whether the disjunction contains a reachability constraint
    ///
    /// A reachability constraint requires at least one location to be empty.
    pub fn contains_reachability_constraint(&self) -> bool {
        self.targets.iter().any(|c| c.is_reachability_constraint())
    }

    /// Get the locations appearing in the specifications
    pub fn get_locations_appearing(&self) -> HashSet<&Location> {
        self.targets
            .iter()
            .map(|t| t.get_locations_appearing())
            .fold(HashSet::new(), |mut acc, x| {
                acc.reserve(x.len());
                acc.extend(x);
                acc
            })
    }

    /// Get the name of the property this target has been derived from
    pub fn name(&self) -> &str {
        &self.property_name
    }

    /// Get the included target configurations
    pub fn get_target_configs(&self) -> impl Iterator<Item = &TargetConfig> {
        self.targets.iter()
    }
}

impl<C: SMTVariableContext<Location> + SMTVariableContext<Variable> + SMTVariableContext<Parameter>>
    EncodeToSMT<DisjunctionTargetConfig, C> for DisjunctionTargetConfig
{
    fn encode_to_smt_with_ctx(
        &self,
        solver: &taco_smt_encoder::SMTSolver,
        ctx: &C,
    ) -> Result<taco_smt_encoder::SMTExpr, SMTSolverError> {
        if self.targets.is_empty() {
            return Ok(solver.false_());
        }

        let disjuncts = self
            .targets
            .iter()
            .map(|c| c.encode_to_smt_with_ctx(solver, ctx))
            .collect::<Result<Vec<_>, SMTSolverError>>()?;

        Ok(solver.or_many(disjuncts))
    }
}

/// Upward closed set of configurations representing a target set of
/// configurations
///
/// This type specifies an upwards closed set of configurations. It can be seen
/// as a minimal basis specifying a set of configurations
#[derive(Debug, Clone, PartialEq)]
pub struct TargetConfig {
    /// Map with location + number of processes at least in there
    /// Set of locations where no process should be
    lower_bounds: HashMap<Location, u32>,
    /// Location should not be covered by any processes
    locations_not_covered: HashSet<Location>,
    /// conjunct of variable constraints
    variable_constr: LIAVariableConstraint,
}

impl And for TargetConfig {
    fn and(mut self, other: Self) -> Self {
        self.lower_bounds.reserve(other.lower_bounds.len());
        self.lower_bounds.extend(other.lower_bounds);

        self.locations_not_covered
            .reserve(other.locations_not_covered.len());
        self.locations_not_covered
            .extend(other.locations_not_covered);

        self.variable_constr = if self.variable_constr == LIAVariableConstraint::True {
            other.variable_constr
        } else if other.variable_constr == LIAVariableConstraint::True {
            self.variable_constr
        } else {
            self.variable_constr & other.variable_constr
        };
        self
    }
}

impl TargetConfig {
    /// Create a new specification object that contains all possible
    /// configurations
    fn new_unconstrained() -> Self {
        TargetConfig {
            lower_bounds: HashMap::new(),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        }
    }

    /// Create a new specification that contains all configurations where `loc`
    /// is not covered by any processes
    fn new_loc_not_covered(loc: Location) -> Self {
        TargetConfig {
            lower_bounds: HashMap::new(),
            locations_not_covered: HashSet::from([loc]),
            variable_constr: LIAVariableConstraint::True,
        }
    }

    /// Create a new specification that requires all configurations in `cover`
    /// to be covered by at least one process
    pub fn new_cover<L: IntoIterator<Item = Location>>(
        cover: L,
    ) -> Result<Self, ReachabilityTransformationError> {
        let locs = cover
            .into_iter()
            .map(|loc| (loc, 1))
            .collect::<HashMap<_, _>>();

        Self::new_reach_with_var_constr(locs, [], BooleanExpression::True)
    }

    /// Create a new specification that requires all configurations in `cover`
    /// to be covered by at the given amount of processes
    pub fn new_general_cover<L: IntoIterator<Item = (Location, u32)>>(
        cover: L,
    ) -> Result<Self, ReachabilityTransformationError> {
        let locs = cover.into_iter().collect::<HashMap<_, _>>();

        Self::new_reach_with_var_constr(locs, [], BooleanExpression::True)
    }

    /// Create a new specification that requires all configurations in `cover`
    /// to be covered by at least one process and all locations in `uncover` to
    /// be empty
    pub fn new_reach<LI: IntoIterator<Item = Location>, LII: IntoIterator<Item = Location>>(
        cover: LI,
        uncover: LII,
    ) -> Result<Self, ReachabilityTransformationError> {
        let cover = cover
            .into_iter()
            .map(|loc| (loc, 1))
            .collect::<HashMap<_, _>>();
        let uncover = uncover.into_iter().collect::<HashSet<_>>();

        Self::new_reach_with_var_constr(cover, uncover, BooleanExpression::True)
    }

    /// Create a new specification that requires all configurations in `cover`
    /// to be covered by at least the specified amount of processes and all
    /// locations in `uncover` to be empty
    pub fn new_general_reach<
        U: IntoIterator<Item = Location>,
        C: IntoIterator<Item = (Location, u32)>,
    >(
        cover: C,
        uncover: U,
    ) -> Result<Self, ReachabilityTransformationError> {
        let cover = cover.into_iter().collect::<HashMap<_, _>>();
        let uncover = uncover.into_iter().collect::<HashSet<_>>();

        Self::new_reach_with_var_constr(cover, uncover, BooleanExpression::True)
    }

    /// Get all locations that appear in the target specification
    pub fn get_locations_appearing(&self) -> HashSet<&Location> {
        self.lower_bounds
            .keys()
            .chain(self.locations_not_covered.iter())
            .collect()
    }

    /// Get the variable constraint appearing in the target configuration
    pub fn get_variable_constraint(&self) -> &LIAVariableConstraint {
        &self.variable_constr
    }

    /// Create a new target configuration constraint
    pub fn new_reach_with_var_constr<
        LC: Into<HashMap<Location, u32>>,
        LU: Into<HashSet<Location>>,
    >(
        locs: LC,
        uncover: LU,
        var_constr: BooleanExpression<Variable>,
    ) -> Result<Self, ReachabilityTransformationError> {
        let lia_constr = (&var_constr).try_into().map_err(|err| {
            ReachabilityTransformationError::VariableConstraintNotLinearArithmetic(err, var_constr)
        })?;

        Ok(TargetConfig {
            lower_bounds: locs.into(),
            locations_not_covered: uncover.into(),
            variable_constr: lia_constr,
        })
    }

    /// Create a new specification contains all configurations where
    /// `var_constr` holds
    fn new_with_var_constr(
        var_constr: BooleanExpression<Variable>,
    ) -> Result<Self, ReachabilityTransformationError> {
        let lia_constr = (&var_constr).try_into().map_err(|err| {
            ReachabilityTransformationError::VariableConstraintNotLinearArithmetic(err, var_constr)
        })?;

        Ok(TargetConfig {
            lower_bounds: HashMap::new(),
            locations_not_covered: HashSet::new(),
            variable_constr: lia_constr,
        })
    }

    /// Check whether this constraint is a reachability constraint
    ///
    /// A reachability constraint requires at least one location to be empty.
    fn is_reachability_constraint(&self) -> bool {
        !self.locations_not_covered.is_empty()
    }

    /// Get iterator over the locations that should be covered by processes with
    /// the least amount of processes
    pub fn get_locations_to_cover(&self) -> impl Iterator<Item = (&Location, &u32)> {
        self.lower_bounds.iter()
    }

    /// Locations that should not be covered
    pub fn get_locations_to_uncover(&self) -> impl Iterator<Item = &Location> {
        self.locations_not_covered.iter()
    }

    /// Create a [`DisjunctionTargetConfig`] with the given name from the single
    /// target location
    pub fn into_disjunct_with_name<S: ToString>(self, name: S) -> DisjunctionTargetConfig {
        DisjunctionTargetConfig::new_with_single_disjunct(name.to_string(), self)
    }

    /// Attempt to parse an [`DisjunctionTargetConfig`] from a location
    /// constraint
    ///
    /// This function can be used to attempt to extract an upwards closed set of
    /// configurations from a single boolean constraint over location variables
    ///
    /// This function returns an error if the specification does not correspond
    /// to an upwards closed set of configurations. See
    fn try_from_loc_constr(
        mut constr: LocConstraint,
    ) -> Result<Self, ReachabilityTransformationError> {
        let single_loc = Threshold::from_integer_comp_expr(constr.0.clone(), constr.2.clone());

        // Handle errors that might occur when attempting to convert into a
        // linear arithmetic
        if let Err(err) = single_loc {
            let err =
                UpwardsClosedSetExtractionError::parse_from_constraint_rewrite_err(err, constr);
            return Err(
                ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(err),
            );
        }
        let (locs, mut thr) = single_loc.unwrap();

        if locs.len() != 1 {
            let err = UpwardsClosedSetExtractionError::LocationConstraintOverMultipleLocs(
                Box::new(constr),
            );

            return Err(
                ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(err),
            );
        }

        // Thresholds including parameters unsupported in reachable constr
        if !thr.is_constant() {
            let err =
                UpwardsClosedSetExtractionError::LocationConstraintWithParameters(Box::new(constr));

            return Err(
                ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(err),
            );
        }

        let (loc, scale) = locs.into_iter().next().unwrap();

        // TODO: refactor this, the logic is actually already in threshold constraint
        if scale.is_negative() {
            thr.scale(-Fraction::from(1));
            constr.1 = constr.1.get_swap_side();
        }

        let c = thr.get_const().unwrap();

        match constr.1 {
            ComparisonOp::Gt | ComparisonOp::Geq => {
                // unconstrained
                if c.is_negative() {
                    return Ok(Self::new_unconstrained());
                }

                let c = if let Ok(c_i64) = i64::try_from(c) {
                    // conversion should be safe now, but check u32 bounds
                    let mut c = match u32::try_from(c_i64) {
                        Ok(val) => val,
                        Err(_) => {
                            // Value out of bounds for u32, notify the user or handle error
                            error!(
                                "Threshold constant {} is out of bounds for u32 (must be between 0 and {}). Truncating to u32::MAX.",
                                c_i64,
                                u32::MAX
                            );
                            u32::MAX
                        }
                    };
                    // in case of `>` need to add 1
                    if constr.1 == ComparisonOp::Gt {
                        if c < u32::MAX {
                            c += 1
                        } else {
                            error!(
                                "Fraction value for lower bound is out of range: {}. Returning unconstrained specification.",
                                constr.1
                            );
                            return Ok(Self::new_unconstrained());
                        }
                    }

                    c
                } else {
                    // TODO: not quite clear whether this is what we want
                    // It might be safer to notify the user
                    let num = c.numerator() as f64;
                    let den = c.denominator() as f64;

                    // take the ceil
                    let lower_bound = (num / den).ceil();
                    lower_bound as u32
                };

                return Self::new_reach_with_var_constr([(loc, c)], [], BooleanExpression::True);
            }
            ComparisonOp::Eq | ComparisonOp::Leq => {
                if c == Fraction::from(0) {
                    return Ok(Self::new_loc_not_covered(loc));
                }
            }
            ComparisonOp::Neq => {
                if c == Fraction::from(0) {
                    return Self::new_cover([loc]);
                }
            }
            ComparisonOp::Lt => {
                if c == Fraction::from(1) {
                    return Ok(Self::new_loc_not_covered(loc));
                }
            }
        }

        let err =
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(Box::new(constr));
        Err(ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(err))
    }
}

impl<C: SMTVariableContext<Location> + SMTVariableContext<Variable> + SMTVariableContext<Parameter>>
    EncodeToSMT<TargetConfig, C> for TargetConfig
{
    fn encode_to_smt_with_ctx(
        &self,
        solver: &taco_smt_encoder::SMTSolver,
        ctx: &C,
    ) -> Result<taco_smt_encoder::SMTExpr, SMTSolverError> {
        // lower bounds
        let lower_bounds = self
            .lower_bounds
            .iter()
            .map(|(loc, n)| {
                let loc = ctx.get_expr_for(loc)?;
                let n = solver.numeral(*n);

                Ok(solver.gte(loc, n))
            })
            .collect::<Result<Vec<_>, SMTSolverError>>()?;

        // locations that should not be covered
        let loc_uncover = self
            .locations_not_covered
            .iter()
            .map(|loc| {
                let loc = ctx.get_expr_for(loc)?;
                let zero = solver.numeral(0);

                Ok(solver.eq(loc, zero))
            })
            .collect::<Result<Vec<_>, SMTSolverError>>()?;

        // constraint on variable evaluation
        let var_constr = self
            .variable_constr
            .as_boolean_expr()
            .encode_to_smt_with_ctx(solver, ctx)?;

        let res = solver.and_many(
            lower_bounds
                .into_iter()
                .chain(loc_uncover)
                .chain([var_constr]),
        );

        Ok(res)
    }
}

impl fmt::Display for TargetConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lower_bounds = join_iterator(
            self.lower_bounds
                .iter()
                .map(|(loc, n)| format!("({loc} >= {n})")),
            " && ",
        );

        let not_covered = join_iterator(
            self.locations_not_covered
                .iter()
                .map(|loc| format!("({loc} == 0)")),
            " && ",
        );

        write!(
            f,
            "{lower_bounds} && {not_covered} && {}",
            self.variable_constr
        )
    }
}

/// Errors that can occur when attempting to extract an upwards closed set of
/// configurations
#[derive(Debug, Clone, PartialEq)]
pub enum UpwardsClosedSetExtractionError {
    /// Location constraint references multiple locations
    ///
    /// The set of such a constraint is not necessarily upwards closed
    LocationConstraintOverMultipleLocs(Box<LocConstraint>),
    /// Constraint for example contains multiplications between locations
    ///
    /// The set of configurations satisfying such a constraint is not necessarily
    /// satisfied
    LocationConstraintNonLinear(Box<LocConstraint>),
    /// Locations constraint references single location but is not necessarily
    /// upwards closed
    LocationConstraintNotUpwardsClosed(Box<LocConstraint>),
    /// Comparison with parameters does not correspond to an upwards closed set
    /// of locations
    LocationConstraintWithParameters(Box<LocConstraint>),
}

impl UpwardsClosedSetExtractionError {
    /// Convert errors from a [`ConstraintRewriteError`] to an
    /// [`UpwardsClosedSetExtractionError`]
    pub fn parse_from_constraint_rewrite_err(
        err: ConstraintRewriteError,
        constr: LocConstraint,
    ) -> Self {
        match err {
            ConstraintRewriteError::NotLinearArithmetic => {
                UpwardsClosedSetExtractionError::LocationConstraintNonLinear(Box::new(constr))
            }
            ConstraintRewriteError::ParameterConstraint(_) => {
                UpwardsClosedSetExtractionError::LocationConstraintWithParameters(Box::new(constr))
            }
        }
    }
}

impl fmt::Display for UpwardsClosedSetExtractionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UpwardsClosedSetExtractionError::LocationConstraintOverMultipleLocs(constr) => {
                write!(
                    f,
                    "Location constraints referencing multiple locations unsupported in clauses behind temporal operators. Clause '{} {} {}' references more than one location",
                    constr.0, constr.1, constr.2
                )
            }
            UpwardsClosedSetExtractionError::LocationConstraintNonLinear(constr) => write!(
                f,
                "Location constraints containing non-linear arithmetic unsupported. Clause '{} {} {}' is not a linear arithmetic expression",
                constr.0, constr.1, constr.2
            ),
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(constr) => {
                write!(
                    f,
                    "Locations constraint does not have an upwards closed set of error states. Such specifications are not supported. Clause '{} {} {}'",
                    constr.0, constr.1, constr.2
                )
            }
            UpwardsClosedSetExtractionError::LocationConstraintWithParameters(constr) => {
                write!(
                    f,
                    "Locations constraint with parameters not supported behind temporal operator. Clause '{} {} {}'",
                    constr.0, constr.1, constr.2
                )
            }
        }
    }
}

impl error::Error for UpwardsClosedSetExtractionError {}

/// Error that can occur during a transformation into a reachability specification
#[derive(Clone, Debug, PartialEq)]
pub enum ReachabilityTransformationError {
    /// Specification is a liveness property
    LivenessSpecification,
    /// Specification contains no upwards closed target
    ReachableConfigurationsNotUpwardsClosed(UpwardsClosedSetExtractionError),
    /// Variable constraint not linear integer arithmetic
    VariableConstraintNotLinearArithmetic(ConstraintRewriteError, BooleanExpression<Variable>),
}

impl fmt::Display for ReachabilityTransformationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LivenessSpecification => write!(
                f,
                "Property contains liveness specification that are not yet supported"
            ),
            Self::ReachableConfigurationsNotUpwardsClosed(err) => {
                write!(
                    f,
                    "Specification extraction failed because the set of error configurations is not upwards closed. Detailed error: {err}"
                )
            }
            Self::VariableConstraintNotLinearArithmetic(rewrite_err, bexpr) => write!(
                f,
                "Specification extraction failed because the variable constraint '{bexpr}'. Detailed error: {rewrite_err}"
            ),
        }
    }
}

impl error::Error for ReachabilityTransformationError {}

impl From<UpwardsClosedSetExtractionError> for ReachabilityTransformationError {
    fn from(value: UpwardsClosedSetExtractionError) -> Self {
        ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(value)
    }
}

/// Alias for unconverted constraints over locations simplifying the definitions
/// in the remainder of the file
///
/// This type corresponds to an expression of the form
/// `BooleanExpression<Location>::ComparisonExpression(Box:.new(0), 1, Box::new(2))`
type LocConstraint = (
    IntegerExpression<Location>,
    ComparisonOp,
    IntegerExpression<Location>,
);

/// Trait for anding two constraints
trait And {
    /// Get the conjunction of `self` and `other`
    fn and(self, other: Self) -> Self;
}

/// Trait for oring two constraints
trait Or {
    /// Get the disjunction of `self` and `other`
    fn or(self, other: Self) -> Self;
}

#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};

    use taco_smt_encoder::{
        SMTSolverBuilder, SMTSolverContext,
        expression_encoding::{EncodeToSMT, SMTVariableContext, StaticSMTContext},
    };
    use taco_threshold_automaton::{
        BooleanVarConstraint,
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp, Location, Parameter,
            Variable,
        },
        general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder,
        lia_threshold_automaton::LIAVariableConstraint,
    };

    use crate::{
        TargetSpec,
        eltl::ELTLExpression,
        reachability_specification::{
            DisjunctionTargetConfig, Reachability, ReachabilityProperty,
            ReachabilityTransformationError, TargetConfig, UpwardsClosedSetExtractionError,
        },
    };

    #[test]
    fn test_target_config_new_cover() {
        let cover = TargetConfig::new_cover([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
        ])
        .unwrap();

        let expected = TargetConfig {
            lower_bounds: HashMap::from([
                (Location::new("l1"), 1),
                (Location::new("l2"), 1),
                (Location::new("l3"), 1),
            ]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(cover, expected);
    }

    #[test]
    fn test_reach_property_new() {
        let cover = TargetConfig::new_cover([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
        ])
        .unwrap()
        .into_disjunct_with_name("test");

        let reach_prop = ReachabilityProperty::new("test", cover);

        let expected = ReachabilityProperty {
            name: "test".into(),
            disj: vec![Reachability {
                precondition_par: Vec::new(),
                precondition_loc: Vec::new(),
                precondition_var: Vec::new(),
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![TargetConfig {
                        lower_bounds: HashMap::from([
                            (Location::new("l1"), 1),
                            (Location::new("l2"), 1),
                            (Location::new("l3"), 1),
                        ]),
                        locations_not_covered: HashSet::new(),
                        variable_constr: LIAVariableConstraint::True,
                    }],
                },
            }],
        };

        assert_eq!(reach_prop, expected);
    }

    #[test]
    fn test_get_target_condition() {
        let cover = TargetConfig::new_cover([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
        ])
        .unwrap()
        .into_disjunct_with_name("test");

        let reach: Reachability = cover.clone().into();
        assert_eq!(reach.get_target_conditions(), &cover);
    }

    #[test]
    fn test_target_config_new_reach() {
        let reach = TargetConfig::new_reach(
            [
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
            ],
            [
                Location::new("l4"),
                Location::new("l5"),
                Location::new("l6"),
            ],
        )
        .unwrap();

        let expected = TargetConfig {
            lower_bounds: HashMap::from([
                (Location::new("l1"), 1),
                (Location::new("l2"), 1),
                (Location::new("l3"), 1),
            ]),
            locations_not_covered: HashSet::from([
                Location::new("l4"),
                Location::new("l5"),
                Location::new("l6"),
            ]),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(reach, expected);
    }

    #[test]
    fn test_target_config_new_reach_with_var_constr() {
        let reach = TargetConfig::new_reach_with_var_constr(
            [
                (Location::new("l1"), 1),
                (Location::new("l2"), 2),
                (Location::new("l3"), 3),
            ],
            [
                Location::new("l4"),
                Location::new("l5"),
                Location::new("l6"),
            ],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let expected = TargetConfig {
            lower_bounds: HashMap::from([
                (Location::new("l1"), 1),
                (Location::new("l2"), 2),
                (Location::new("l3"), 3),
            ]),
            locations_not_covered: HashSet::from([
                Location::new("l4"),
                Location::new("l5"),
                Location::new("l6"),
            ]),
            variable_constr: (&BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ))
                .try_into()
                .unwrap(),
        };

        assert_eq!(reach, expected);
    }

    // This test tests a private method but this method is crucial for correctness
    #[test]
    fn test_target_config_try_loc_constr_translatable_cases() {
        // l == 0
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::new(),
            locations_not_covered: HashSet::from([Location::new("l")]),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l != 0
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Neq,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 1)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l > 0
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 1)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l > 42
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::Const(42),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 43)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l >= 42
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Geq,
            IntegerExpression::Const(42),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 42)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l > 2/3
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(2)),
                IntegerOp::Div,
                Box::new(IntegerExpression::Const(3)),
            ),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 1)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l >= 2/3
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(2)),
                IntegerOp::Div,
                Box::new(IntegerExpression::Const(3)),
            ),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 1)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        //  42 < l --> l > 42
        let test_expr = (
            IntegerExpression::Const(42),
            ComparisonOp::Lt,
            IntegerExpression::Atom(Location::new("l")),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok(), "{:#?}", got);

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 43)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l > 0 + 1 + 2
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Gt,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(0)),
                IntegerOp::Add,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(1)),
                    IntegerOp::Add,
                    Box::new(IntegerExpression::Const(2)),
                )),
            ),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::from([(Location::new("l"), 4)]),
            locations_not_covered: HashSet::new(),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l < 1
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Lt,
            IntegerExpression::Const(1),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::new(),
            locations_not_covered: HashSet::from([Location::new("l")]),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);

        // l <= 0
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Leq,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr);
        assert!(got.is_ok());

        let expected = TargetConfig {
            lower_bounds: HashMap::new(),
            locations_not_covered: HashSet::from([Location::new("l")]),
            variable_constr: LIAVariableConstraint::True,
        };

        assert_eq!(got.unwrap(), expected);
    }

    // This test tests a private method but this method is crucial for correctness
    #[test]
    fn test_target_config_try_loc_constr_error_cases() {
        // l1 + l2 == 0
        let test_expr = (
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                IntegerOp::Add,
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
            ),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err(), "{:#?}", got);

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintOverMultipleLocs(Box::new(
                test_expr,
            )),
        );
        assert_eq!(got.unwrap_err(), expected);

        // l * l == 0
        let test_expr = (
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                IntegerOp::Mul,
                Box::new(IntegerExpression::Atom(Location::new("l"))),
            ),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err());

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintNonLinear(Box::new(test_expr)),
        );
        assert_eq!(got.unwrap_err(), expected);

        // l + n == 0
        let test_expr = (
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                IntegerOp::Add,
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err());

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintWithParameters(Box::new(test_expr)),
        );
        assert_eq!(got.unwrap_err(), expected);

        // l < 3
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Lt,
            IntegerExpression::Const(3),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err());

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(Box::new(
                test_expr,
            )),
        );
        assert_eq!(got.unwrap_err(), expected);

        // l <= 3
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Leq,
            IntegerExpression::Const(3),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err());

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(Box::new(
                test_expr,
            )),
        );
        assert_eq!(got.unwrap_err(), expected);

        // l == 3
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Eq,
            IntegerExpression::Const(3),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err());

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(Box::new(
                test_expr,
            )),
        );
        assert_eq!(got.unwrap_err(), expected);

        // l != 3
        let test_expr = (
            IntegerExpression::Atom(Location::new("l")),
            ComparisonOp::Neq,
            IntegerExpression::Const(3),
        );

        let got = TargetConfig::try_from_loc_constr(test_expr.clone());
        assert!(got.is_err());

        let expected = ReachabilityTransformationError::ReachableConfigurationsNotUpwardsClosed(
            UpwardsClosedSetExtractionError::LocationConstraintNotUpwardsClosed(Box::new(
                test_expr,
            )),
        );
        assert_eq!(got.unwrap_err(), expected);
    }

    #[test]
    fn test_target_config_encode_target_config_unconstrained() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [], []).unwrap();

        let config = TargetConfig::new_unconstrained();

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let expected_expr = ctx.get_true();
        assert_eq!(got_expr, expected_expr)
    }

    #[test]
    fn test_target_config_encode_target_config_single_loc_cov() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [Location::new("l")], []).unwrap();

        let config = TargetConfig::new_cover([Location::new("l")]).unwrap();

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and(
            solver.gte(
                ctx.get_expr_for(&Location::new("l")).unwrap(),
                solver.numeral(1),
            ),
            solver.true_(),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_encode_target_config_single_loc_uncover() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [Location::new("l")], []).unwrap();

        let config = TargetConfig::new_loc_not_covered(Location::new("l"));

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and(
            solver.eq(
                ctx.get_expr_for(&Location::new("l")).unwrap(),
                solver.numeral(0),
            ),
            solver.true_(),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_encode_target_config_var_constr() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            solver_builder,
            [],
            [Location::new("l")],
            [Variable::new("v")],
        )
        .unwrap();

        let config = TargetConfig::new_with_var_constr(BooleanVarConstraint::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("v"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        ))
        .unwrap();

        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and(
            solver.lt(
                ctx.get_expr_for(&Variable::new("v")).unwrap(),
                solver.numeral(2),
            ),
            solver.gte(
                ctx.get_expr_for(&Variable::new("v")).unwrap(),
                solver.numeral(1),
            ),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_encode_target_config_all_constr() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            solver_builder,
            [],
            [Location::new("l1"), Location::new("l2")],
            [Variable::new("v")],
        )
        .unwrap();

        let config = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [Location::new("l2")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();
        let got_expr = config
            .encode_to_smt_with_ctx(ctx.get_smt_solver(), &ctx)
            .unwrap();

        let solver = ctx.get_smt_solver();

        let expected_expr = solver.and_many([
            solver.gte(
                ctx.get_expr_for(&Location::new("l1")).unwrap(),
                solver.numeral(42),
            ),
            solver.eq(
                ctx.get_expr_for(&Location::new("l2")).unwrap(),
                solver.numeral(0),
            ),
            solver.and(
                solver.lt(
                    ctx.get_expr_for(&Variable::new("v")).unwrap(),
                    solver.numeral(2),
                ),
                solver.gte(
                    ctx.get_expr_for(&Variable::new("v")).unwrap(),
                    solver.numeral(1),
                ),
            ),
        ]);

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_target_config_locations_appearing() {
        let config = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [Location::new("l2")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let got_expr: HashSet<Location> = config
            .get_locations_appearing()
            .into_iter()
            .cloned()
            .collect();

        let expected_locs = HashSet::from([Location::new("l1"), Location::new("l2")]);

        assert_eq!(got_expr, expected_locs)
    }

    #[test]
    fn test_target_config_is_reachability_constr() {
        let config = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [Location::new("l2")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        assert!(config.is_reachability_constraint());

        let config = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        assert!(!config.is_reachability_constraint());
    }

    #[test]
    fn test_disjunction_target_config_get_locations_in_target() {
        let config1 = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [Location::new("l2")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let config2 = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l3"), 42)],
            [Location::new("l4")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let dis = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![config1, config2],
        };

        let got_set_locations: HashSet<Location> =
            dis.get_locations_in_target().into_iter().cloned().collect();

        let expected_set_locations = HashSet::from([
            Location::new("l1"),
            Location::new("l2"),
            Location::new("l3"),
            Location::new("l4"),
        ]);

        assert_eq!(got_set_locations, expected_set_locations);

        let dis = DisjunctionTargetConfig::new_empty("test".into());

        let got_set_locations: HashSet<_> = dis.get_locations_in_target().into_iter().collect();

        let expected_set_locations = HashSet::from([]);

        assert_eq!(got_set_locations, expected_set_locations);
    }

    #[test]
    fn test_disj_target_config_contains_reachability_constraint() {
        let config1 = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let config2 = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l3"), 42)],
            [Location::new("l4")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let dis = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![config1, config2],
        };

        assert!(dis.contains_reachability_constraint());

        let disj = DisjunctionTargetConfig::new_empty("test".into());

        assert!(!disj.contains_reachability_constraint())
    }

    #[test]
    fn test_disj_target_config_encode_to_smt_empty() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(solver_builder, [], [], []).unwrap();

        let solver = ctx.get_smt_solver();

        let disj = DisjunctionTargetConfig::new_empty("test".into());

        let got_expr = disj.encode_to_smt_with_ctx(solver, &ctx).unwrap();

        let expected_expr = solver.false_();

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_disj_target_config_encode_smt() {
        let solver_builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            solver_builder,
            [],
            [
                Location::new("l1"),
                Location::new("l2"),
                Location::new("l3"),
                Location::new("l4"),
            ],
            [Variable::new("v")],
        )
        .unwrap();

        let solver = ctx.get_smt_solver();

        let config1 = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l1"), 42)],
            [Location::new("l2")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let config2 = TargetConfig::new_reach_with_var_constr(
            [(Location::new("l3"), 42)],
            [Location::new("l4")],
            BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ),
        )
        .unwrap();

        let disj = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![config1, config2],
        };

        let got_expr = disj.encode_to_smt_with_ctx(solver, &ctx).unwrap();

        let expected_expr = solver.or_many([
            solver.and_many([
                solver.gte(
                    ctx.get_expr_for(&Location::new("l1")).unwrap(),
                    solver.numeral(42),
                ),
                solver.eq(
                    ctx.get_expr_for(&Location::new("l2")).unwrap(),
                    solver.numeral(0),
                ),
                solver.and(
                    solver.lt(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(2),
                    ),
                    solver.gte(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(1),
                    ),
                ),
            ]),
            solver.and_many([
                solver.gte(
                    ctx.get_expr_for(&Location::new("l3")).unwrap(),
                    solver.numeral(42),
                ),
                solver.eq(
                    ctx.get_expr_for(&Location::new("l4")).unwrap(),
                    solver.numeral(0),
                ),
                solver.and(
                    solver.lt(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(2),
                    ),
                    solver.gte(
                        ctx.get_expr_for(&Variable::new("v")).unwrap(),
                        solver.numeral(1),
                    ),
                ),
            ]),
        ]);

        assert_eq!(
            got_expr,
            expected_expr,
            "got: {}, expected: {}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_reachability_property_get_name() {
        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![],
        };

        assert_eq!(reach_property.name(), "test")
    }

    #[test]
    fn test_reachability_property_contains_reachability_constraint() {
        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![],
        };
        assert!(!reach_property.contains_reachability_constraint());

        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![TargetConfig::new_loc_not_covered(Location::new("l"))],
                },
            }],
        };
        assert!(reach_property.contains_reachability_constraint());
    }

    #[test]
    fn test_reachability_property_create_tas() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .with_location(Location::new("l"))
            .unwrap()
            .with_variable(Variable::new("v"))
            .unwrap()
            .initialize()
            .build();

        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![],
        };
        assert_eq!(reach_property.create_tas_to_check(&ta).count(), 0);

        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(42)),
                )],
                precondition_loc: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![],
                },
            }],
        };
        let mut it = reach_property.create_tas_to_check(&ta);
        let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta-test")
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .with_location(Location::new("l"))
            .unwrap()
            .with_variable(Variable::new("v"))
            .unwrap()
            .initialize()
            .with_resilience_condition(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .unwrap()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ))
            .unwrap()
            .build();
        let expected_disj = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![],
        };
        assert_eq!(it.next().unwrap(), (expected_disj, expected_ta));
        assert_eq!(it.next(), None);

        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(42)),
                )],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![],
                },
            }],
        };
        let mut it = reach_property.create_tas_to_check(&ta);
        let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta-test")
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .with_location(Location::new("l"))
            .unwrap()
            .with_variable(Variable::new("v"))
            .unwrap()
            .initialize()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .unwrap()
            .build();
        let expected_disj = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![],
        };
        assert_eq!(it.next().unwrap(), (expected_disj, expected_ta));
        assert_eq!(it.next(), None);

        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(42)),
                )],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_unconstrained(),
                        TargetConfig::new_cover([Location::new("l")]).unwrap(),
                    ],
                },
            }],
        };
        let mut it = reach_property.create_tas_to_check(&ta);
        let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta-test")
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .with_location(Location::new("l"))
            .unwrap()
            .with_variable(Variable::new("v"))
            .unwrap()
            .initialize()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .unwrap()
            .build();
        let expected_disj = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![
                TargetConfig::new_unconstrained(),
                TargetConfig::new_cover([Location::new("l")]).unwrap(),
            ],
        };
        assert_eq!(it.next().unwrap(), (expected_disj, expected_ta));
        assert_eq!(it.next(), None);

        let reach_property = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![
                Reachability {
                    precondition_par: vec![],
                    precondition_loc: vec![BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(42)),
                    )],
                    precondition_var: vec![],
                    target: DisjunctionTargetConfig {
                        targets: vec![],
                        property_name: "test".into(),
                    },
                },
                Reachability {
                    precondition_par: vec![],
                    precondition_loc: vec![BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(42)),
                    )],
                    precondition_var: vec![],
                    target: DisjunctionTargetConfig {
                        property_name: "test".into(),
                        targets: vec![],
                    },
                },
            ],
        };
        let mut it = reach_property.create_tas_to_check(&ta);
        let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta-test")
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .with_location(Location::new("l"))
            .unwrap()
            .with_variable(Variable::new("v"))
            .unwrap()
            .initialize()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .unwrap()
            .build();
        let expected_disj = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![],
        };
        assert_eq!(it.next().unwrap(), (expected_disj, expected_ta));
        let expected_disj = DisjunctionTargetConfig {
            property_name: "test".into(),
            targets: vec![],
        };
        let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta-test")
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .with_location(Location::new("l"))
            .unwrap()
            .with_variable(Variable::new("v"))
            .unwrap()
            .initialize()
            .with_initial_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .unwrap()
            .build();
        assert_eq!(it.next().unwrap(), (expected_disj, expected_ta));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_reachability_property_from_eltl() {
        // true -> false -> Must be empty disjunct
        let eltl = ELTLExpression::True;

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![],
        };

        assert_eq!(got_reach, expected_reach);

        // false -> true -> any location
        let eltl = ELTLExpression::False;

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability::new_unconstrained("test".into())],
        };

        assert_eq!(got_reach, expected_reach);

        // n == 3 -> n != 3
        let eltl = ELTLExpression::ParameterExpr(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(3)),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(3)),
                )],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig::new_empty("test".into()),
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // v < n -> v > n
        let eltl = ELTLExpression::VariableExpr(
            Box::new(IntegerExpression::Atom(Variable::new("v"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                )],
                target: DisjunctionTargetConfig::new_empty("test".into()),
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // l < n -> v > n
        let eltl = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("l"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                )],
                precondition_var: vec![],
                target: DisjunctionTargetConfig::new_empty("test".into()),
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // (l < 1) && (v < 3)  -> (l >= 1) || (v >= 3)
        let eltl = ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(3)),
            )),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![
                Reachability {
                    precondition_par: vec![],
                    precondition_loc: vec![BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1)),
                    )],
                    precondition_var: vec![],
                    target: DisjunctionTargetConfig::new_empty("test".into()),
                },
                Reachability {
                    precondition_par: vec![],
                    precondition_loc: vec![],
                    precondition_var: vec![BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    )],
                    target: DisjunctionTargetConfig::new_empty("test".into()),
                },
            ],
        };

        assert_eq!(got_reach, expected_reach);

        // (l < 1) || (v < 3)  -> (l >= 1) && (v >= 3)
        let eltl = ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(3)),
            )),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![
                Reachability {
                    precondition_par: vec![],
                    precondition_loc: vec![BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1)),
                    )],
                    precondition_var: vec![],
                    target: DisjunctionTargetConfig::new_empty("test".into()),
                },
                Reachability {
                    precondition_par: vec![],
                    precondition_loc: vec![],
                    precondition_var: vec![BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    )],
                    target: DisjunctionTargetConfig::new_empty("test".into()),
                },
            ],
        };

        assert_eq!(got_reach, expected_reach);

        // !((l < 1) && (v < 3))  -> ((l < 1) && (v < 3))
        let eltl = ELTLExpression::Not(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(3)),
            )),
        )));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("l"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(1)),
                )],
                precondition_var: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(3)),
                )],
                target: DisjunctionTargetConfig::new_empty("test".into()),
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](true) -> <>(false)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::True));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](false) -> <>(true)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::False));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![TargetConfig::new_unconstrained()],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](v < n) -> <>(v >= n)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::VariableExpr(
            Box::new(IntegerExpression::Atom(Variable::new("v"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        )));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_with_var_constr(BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("v"))),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ))
                        .unwrap(),
                    ],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](l == 0) -> <>(l > 1)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("l"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        )));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![TargetConfig::new_cover([Location::new("l")]).unwrap()],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](l1 == 0 || l2 != 0) -> <>(l1 != 0 && l2 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(0)),
            )),
        )));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_reach([Location::new("l1")], [Location::new("l2")])
                            .unwrap(),
                    ],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](l1 == 0 && l2 != 0) -> <>(l1 != 0 || l2 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(0)),
            )),
        )));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_cover([Location::new("l1")]).unwrap(),
                        TargetConfig::new_loc_not_covered(Location::new("l2")),
                    ],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // []([](l1 == 0 || l2 != 0)) -> <>(l1 != 0 && l2 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::Globally(Box::new(
            ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            ),
        ))));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_reach([Location::new("l1")], [Location::new("l2")])
                            .unwrap(),
                    ],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // [](l1 == 0 || [](l2 != 0)) -> <>(l1 != 0 && l2 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_reach([Location::new("l1")], [Location::new("l2")])
                            .unwrap(),
                    ],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // (v == 0) =>  [](l1 == 0 || [](l2 != 0))
        let eltl = ELTLExpression::Implies(
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l2"))),
                        ComparisonOp::Neq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )))),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![],
                precondition_var: vec![BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![
                        TargetConfig::new_reach([Location::new("l1")], [Location::new("l2")])
                            .unwrap(),
                    ],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);

        // !(l1 == 0) || [](l2 == 0)
        let eltl = ELTLExpression::Or(
            Box::new(ELTLExpression::Not(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )))),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got_reach = ReachabilityProperty::from_named_eltl("test", eltl).unwrap();

        let expected_reach = ReachabilityProperty {
            name: "test".to_string(),
            disj: vec![Reachability {
                precondition_par: vec![],
                precondition_loc: vec![
                    BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ],
                precondition_var: vec![],
                target: DisjunctionTargetConfig {
                    property_name: "test".into(),
                    targets: vec![TargetConfig::new_reach([Location::new("l2")], []).unwrap()],
                },
            }],
        };

        assert_eq!(got_reach, expected_reach);
    }
}

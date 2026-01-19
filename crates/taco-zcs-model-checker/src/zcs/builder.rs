//! Factory method to construct a symbolic 01-CS (ZCS) for a given IntervalThresholdAutomaton

use std::fmt::Debug;

use taco_bdd::{BDD, BDDManager, BddManager};
use taco_interval_ta::IntervalActionEffect;
use taco_interval_ta::{IntervalConstraint, IntervalTARule, IntervalThresholdAutomaton};
use taco_threshold_automaton::ActionDefinition;
use taco_threshold_automaton::RuleDefinition;
use taco_threshold_automaton::expressions::Variable;

use taco_threshold_automaton::ThresholdAutomaton;

use crate::zcs::bdd_var_manager::BddVarManager;

use super::{Bdd, SymbolicTransition, ZCS, ZCSStates};

/// Builder for constructing a symbolic 01-CS
///
/// This builder takes a BDDManager and an IntervalThresholdAutomaton
/// and derives the corresponding symbolic 01-counter system (ZCS).
///
/// The builder encodes the initial states, the symbolic transitions for each rule,
/// and the symbolic transition relation as a single BDD.
#[derive(Debug)]
pub struct ZCSBuilder<'a> {
    /// 01-CS (ZCS) that is constructed by the builder
    cs: ZCS<'a>,
}
impl<'a> ZCSBuilder<'a> {
    /// create a new symbolic 01-CS builder
    pub fn new(mgr: &BDDManager, aut: &'a IntervalThresholdAutomaton) -> Self {
        ZCSBuilder {
            cs: ZCS {
                bdd_mgr: BddVarManager::new(mgr.clone(), aut),
                ata: aut,
                initial_states: ZCSStates {
                    set_of_states: mgr.get_bdd_false(),
                },
                transitions: Vec::new(),
                transition_relation: mgr.get_bdd_false(),
            },
        }
    }

    /// 1. encode initial states
    /// 2. encode each rule as a transition bdd
    /// 3. encode entire transition relation
    pub fn initialize(&mut self) {
        self.cs.initial_states = self.build_initial_states();
        self.cs.transitions = self.build_symbolic_transitions();
        self.cs.transition_relation = self.build_symbolic_transition_relation();
    }

    /// Build the bdd that represents the set of initial states
    fn build_initial_states(&self) -> ZCSStates {
        // add initial locations
        // collect bdds of all states that are not initial and negate them
        let initial_states_bdd = self
            .cs
            .ata
            .locations()
            .filter(|loc| !self.cs.ata.can_be_initial_location(loc))
            .map(|loc| {
                !self
                    .cs
                    .bdd_mgr
                    .get_location_var(loc)
                    .unwrap_or_else(|_| panic!("No bdd variable for location {loc} created"))
            })
            .fold(self.cs.bdd_mgr.get_bdd_true(), |acc, bdd| acc & bdd);

        // add initial intervals
        let initial_states_bdd =
            self.cs
                .ata
                .variables()
                .fold(initial_states_bdd, |acc, var| {
                    let initial_intervals = self.cs.ata.get_initial_interval(var);
                    acc.and(
                        &initial_intervals.into_iter().map(|initial_interval|{
                            self
                            .cs
                            .bdd_mgr
                            .get_shared_interval_bdd(var, initial_interval)
                            .unwrap_or_else(|_| panic!("No shared interval bdd for shared variable {var} and interval {initial_interval} created"))
                        }).fold(self.cs.bdd_mgr.get_bdd_false(), |acc, bdd| {
                            acc.or(bdd)
                        }
                    ))
                });

        ZCSStates::new(initial_states_bdd)
    }

    /// builds all symbolic transitions for all rules of the TA
    fn build_symbolic_transitions(&self) -> Vec<SymbolicTransition> {
        self.cs
            .ata
            .rules()
            .map(|rule| self.build_symbolic_transition(rule))
            .collect()
    }

    /// Build a symbolic transition for a given rule of the threshold automaton
    ///
    /// # Steps
    ///   1. constraints for locations
    ///   2. add encoded rule_id to symbolic_transition
    ///   3. check if abstract guard is satisfied
    ///   4. check if effects of rule are applied. i.e., effects of update vector and resets
    fn build_symbolic_transition(&self, rule: &IntervalTARule) -> SymbolicTransition {
        //   1. constraints for locations
        let mut symbolic_transition = self.build_location_constraints_for_rule(rule);

        // 2. add encoded rule_id to symbolic_transition
        symbolic_transition &= self
            .cs
            .bdd_mgr
            .get_rule_bdd(rule)
            .unwrap_or_else(|_| panic!("No bdd variable for rule {rule} created"))
            .clone();

        // 3. check if abstract guard is satisfied (single and multi var guard)
        symbolic_transition &= self.construct_bdd_guard(rule.get_guard());

        // 4. check if effects of rule are applied. i.e., effects of update vector and resets
        symbolic_transition &= self.build_effect_constraints_for_rule(rule);

        // return symbolic transition
        SymbolicTransition {
            abstract_rule: rule.clone(),
            transition_bdd: symbolic_transition,
        }
    }

    /// builds location constraints for a given `rule` from location `from` to location `to`
    ///
    /// 1. `from` and `to_prime` have to be set
    /// 2. `from_prime` and `to` can either be either empty or occupied, the value for all other locations has to be equal
    fn build_location_constraints_for_rule(&self, rule: &IntervalTARule) -> BDD {
        // 1. `from` and `to_prime` have to be set
        let loc_constraint = self
            .cs
            .bdd_mgr
            .get_location_var(rule.source())
            .unwrap_or_else(|_| panic!("No bdd variable for location {} created", rule.source()))
            .and(
                self.cs
                    .bdd_mgr
                    .get_primed_location_var(rule.target())
                    .unwrap_or_else(|_| {
                        panic!(
                            "No primed bdd variable for location {} created",
                            rule.target()
                        )
                    }),
            );

        // 2. 'from_prime' and 'to' can either be either empty or occupied, the value for all other locations has to be equal
        self.cs
            .ata
            .locations()
            .filter(|loc| *loc != rule.source() && *loc != rule.target())
            .fold(loc_constraint, |acc, loc| {
                acc & self
                    .cs
                    .bdd_mgr
                    .get_location_var(loc)
                    .unwrap_or_else(|_| panic!("No bdd variable for location {loc} created"))
                    .equiv(
                        self.cs
                            .bdd_mgr
                            .get_primed_location_var(loc)
                            .unwrap_or_else(|_| {
                                panic!("No primed bdd variable for location {loc} created")
                            }),
                    )
            })
    }

    /// builds the guard constraints for a given rule
    ///
    /// 1. reset -> primed interval is the initial interval, i.e., I_0 = [0,1)
    /// 2. increment/decrement -> primed interval is the next/previous interval or stays in the same interval
    /// 3. no effect -> primed interval stays in the same interval
    fn build_effect_constraints_for_rule(&self, rule: &IntervalTARule) -> BDD {
        let effect_constraints = rule
            .actions()
            .fold(self.cs.bdd_mgr.get_bdd_true(), |acc, act| {
                let var = act.variable();
                let effect = act.effect();

                // 1. reset -> primed interval is the initial interval, i.e., I_0 = [0,1)
                if matches!(effect, IntervalActionEffect::Reset) {
                    let primed_initial_interval_bdd =
                        self.build_reset_constraints_for_shared_var(var);

                    acc.and(primed_initial_interval_bdd)
                } else {
                    // 2. increment/decrement -> primed interval is the next/previous interval or stays in the same interval
                    let update_constraints =
                        self.build_update_constraints_for_shared_var(var, effect);
                    acc.and(&update_constraints)
                }
            });

        // 3. no effect -> primed interval stays in the same interval
        self.cs
            .ata
            .variables()
            .filter(|var| !rule.updates_variable(var))
            .fold(effect_constraints, |acc, var| {
                acc & self
                    .cs
                    .bdd_mgr
                    .get_unchanged_interval_bdd(var)
                    .unwrap_or_else(|_| {
                        panic!(
                            "No unchanged interval bdd for shared variable {var} could be created"
                        )
                    })
            })
    }

    /// builds the reset constraint for a given shared variable
    /// i.e., the primed interval is the initial interval I_0 = [0,1)
    fn build_reset_constraints_for_shared_var(&self, shared: &Variable) -> &BDD {
        let initial_interval = &self.cs.ata.get_zero_interval(shared);

        self
            .cs
            .bdd_mgr
            .get_primed_shared_interval_bdd(shared, initial_interval)
            .unwrap_or_else(|_| panic!("No primed interval bdd for shared variable {shared} and interval {initial_interval} created"))
    }

    /// builds the update constraint for a given shared variable for `effect` which is either a increment or decrement
    /// i.e., the primed interval is the next/previous interval or stays in the same interval
    fn build_update_constraints_for_shared_var(
        &self,
        shared: &Variable,
        effect: &IntervalActionEffect,
    ) -> BDD {
        self.cs.ata.get_intervals(shared).iter().fold(
            self.cs.bdd_mgr.get_bdd_true(),
            |acc, interval| {
                let unprimed_interval_bdd = self
                    .cs
                    .bdd_mgr
                    .get_shared_interval_bdd(shared, interval)
                    .unwrap_or_else(|_| panic!("No interval bdd for shared variable {shared} and interval {interval} created"));

                let unchanged_primed_interval_bdd = self
                    .cs
                    .bdd_mgr
                    .get_primed_shared_interval_bdd(shared, interval)
                    .unwrap_or_else(|_| panic!("No primed interval bdd for shared variable {shared} and interval {interval} created"));

                let succ_primed_interval = match effect {
                    IntervalActionEffect::Inc(_) => self.cs.ata.get_next_interval(shared, interval),
                    IntervalActionEffect::Dec(_) => {
                        self.cs.ata.get_previous_interval(shared, interval)
                    }
                    IntervalActionEffect::Reset => unreachable!(),
                };

                // there is no next interval -> only possible to stay in the current interval
                let mut possible_intervals = unchanged_primed_interval_bdd.clone();
                if let Some(next) = succ_primed_interval {
                    //there is a next interval -> either stay in interval or move to next/previous one
                    let next_bdd = self
                        .cs
                        .bdd_mgr
                        .get_primed_shared_interval_bdd(shared, next)
                        .unwrap_or_else(|_| panic!("No primed interval bdd for shared variable {shared} and interval {next} created"));
                    // interval is a constant of the form [n,n+1) -> then there is no unchanged interval
                    // i.e., applying the rule one time always leads to the next interval
                    if interval.check_add_always_out_of_interval(1) {
                        possible_intervals = next_bdd.clone();
                    } else {
                        possible_intervals |= next_bdd.clone();
                    }
                }
                acc.and(&unprimed_interval_bdd.implies(&possible_intervals))
            },
        )
    }

    /// builds the symbolic transition relation as a single bdd
    /// assume that all symbolic transitions are already stored in the cs
    fn build_symbolic_transition_relation(&self) -> BDD {
        self.cs.transitions.iter().fold(
            self.cs.bdd_mgr.get_bdd_false(),
            |acc, symbolic_transition| acc.or(&symbolic_transition.transition_bdd),
        )
    }

    /// Given an abstract guard as an IntervalGuard,
    /// Construct a BDD that replaces every abstract Interval with its respective BDD
    fn construct_bdd_guard(&self, guard: &IntervalConstraint) -> BDD {
        match guard {
            IntervalConstraint::True => self.cs.bdd_mgr.get_bdd_true(),
            IntervalConstraint::Conj(lhs, rhs) => {
                let lhs_bdd = self.construct_bdd_guard(lhs);
                let rhs_bdd = self.construct_bdd_guard(rhs);
                lhs_bdd.and(&rhs_bdd)
            }
            IntervalConstraint::Disj(lhs, rhs) => {
                let lhs_bdd = self.construct_bdd_guard(lhs);
                let rhs_bdd = self.construct_bdd_guard(rhs);
                lhs_bdd.or(&rhs_bdd)
            }
            IntervalConstraint::SingleVarIntervalConstr(variable, hash_set) => {
                let mut possible_intervals = self.cs.bdd_mgr.get_bdd_false();
                for interval in hash_set {
                    possible_intervals = possible_intervals.or(self
                        .cs
                        .bdd_mgr
                        .get_shared_interval_bdd(variable, interval)
                        .unwrap_or_else(|_| panic!("No interval bdd for shared variable {variable} and interval {interval} created")));
                }
                possible_intervals
            }
            IntervalConstraint::MultiVarIntervalConstr(_, _) => {
                unimplemented!("No support for multivar variables yet")
            }
            IntervalConstraint::False => self.cs.bdd_mgr.get_bdd_false(),
        }
    }

    /// build the symbolic 01-CS
    pub fn build(mut self) -> ZCS<'a> {
        self.initialize();
        self.cs
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use taco_interval_ta::builder::IntervalTABuilder;

    use taco_interval_ta::interval::Interval;
    use taco_interval_ta::interval::IntervalBoundary;

    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::expressions::Location;
    use taco_threshold_automaton::expressions::Variable;
    use taco_threshold_automaton::expressions::fraction::Fraction;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::Threshold;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::WeightedSum;
    use taco_threshold_automaton::{
        BooleanVarConstraint, LocationConstraint, ParameterConstraint,
        expressions::{ComparisonOp, IntegerExpression, Parameter},
        general_threshold_automaton::{Action, builder::RuleBuilder},
    };

    /// This function creates the canonical threshold automaton
    /// for a simple voting algorithm,
    /// presented in Figure 1 from the paper
    /// "Parameterized Verification of Round-based Distributed Algorithms
    /// via Extended Threshold Automata" (FM24)
    ///
    /// i.e.,
    /// Locations: { v0, v1, wait, d0, d1 }
    /// Variables: { x0, x1 }
    /// Parameters: { n, t, f }
    /// Initial location constraints: v0 + v1 = n - t & wait = 0 & d0 = 0 & d1 = 0
    /// Resilience Condition: n > 3 * t & t >= f
    /// Rules:
    ///     r0: v0 -> wait, guard: true, action: x0 = x0 + 1
    ///     r1: v1 -> wait, guard: true, action: x1 = x1 + 1
    ///     r2: wait -> d0, guard: x0 >= n - t, action: none
    ///     r3: wait -> d1, guard: x1 >= n - t, action: none
    ///
    /// Abstract Threshold Automaton:
    /// Intervals for x0 and x1: I_0 = [0,1), I_1 = [1,n-t), I_2 = [n-t, infty)
    /// Interval Order: I_0 < I_1 < I_2
    /// Abstract Rules:
    ///     r0: v0 -> wait, guard: true, action: x0 = x0 + 1
    ///     r1: v1 -> wait, guard: true, action: x1 = x1 + 1
    ///     r2: wait -> d0, guard: x0 = I_2, action: none
    ///     r3: wait -> d1, guard: x1 = I_2, action: none
    fn test_automaton() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![
                    Location::new("v0"),
                    Location::new("v1"),
                    Location::new("wait"),
                    Location::new("d0"),
                    Location::new("d1"),
                ])
                .unwrap()
                .with_variables(vec![Variable::new("x0"), Variable::new("x1")])
                .unwrap()
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                ])
                .unwrap()
                .initialize()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(
                            IntegerExpression::Atom(Location::new("v0"))
                                + IntegerExpression::Atom(Location::new("v1")),
                        ),
                        ComparisonOp::Eq,
                        Box::new(
                            IntegerExpression::Param(Parameter::new("n"))
                                - IntegerExpression::Param(Parameter::new("t")),
                        ),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("wait"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("d0"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("d1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_resilience_conditions(vec![
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                        ComparisonOp::Gt,
                        Box::new(
                            IntegerExpression::Const(3)
                                * IntegerExpression::Atom(Parameter::new("t")),
                        ),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("t"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Parameter::new("n")) - IntegerExpression::Atom(Parameter::new("t"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(1)),
                    ),

                ])
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("v0"), Location::new("wait"))
                        .with_action(
                            Action::new(
                                Variable::new("x0"),
                                IntegerExpression::Atom(Variable::new("x0"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(1, Location::new("v1"), Location::new("wait"))
                        .with_action(
                            Action::new(
                                Variable::new("x1"),
                                IntegerExpression::Atom(Variable::new("x1"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(2, Location::new("wait"), Location::new("d0"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x0"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .build(),
                    RuleBuilder::new(3, Location::new("wait"), Location::new("d1"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x1"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .build(),
                ])
                .unwrap();
        let ta = ta_builder.build();
        let lia =
            taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton::try_from(
                ta.clone(),
            )
            .unwrap();

        let mut interval_tas = IntervalTABuilder::new(lia, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_threshold_automaton = interval_tas.next().unwrap();

        let nxt = interval_tas.next();
        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());

        interval_threshold_automaton
    }

    /// This function creates a very basic threshold automaton with one decrement rule and one reset rule
    ///
    /// Intervals for shared variable: I_0 = [0,1), I_1 = [1,n-t), I_2 = [n-t,infty)
    /// r0: l0 -> l1: x = x - 1
    /// r1: l0 -> l1: x = 0
    fn test_dec_reset_automaton() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![Location::new("l0"), Location::new("l1")])
                .unwrap()
                .with_variable(Variable::new("x"))
                .unwrap()
                .with_parameters(vec![Parameter::new("n"), Parameter::new("t")])
                .unwrap()
                .initialize().with_resilience_condition(ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Parameter::new("n")) - IntegerExpression::Atom(Parameter::new("t"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )).unwrap().with_initial_variable_constraint(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Geq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("t")),
                    ),
                )).unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("l0"), Location::new("l1"))
                        .with_action(
                            Action::new(
                                Variable::new("x"),
                                IntegerExpression::Atom(Variable::new("x"))
                                    - IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(1, Location::new("l0"), Location::new("l1"))
                        .with_action(Action::new_reset(Variable::new("x")))
                        .build(),
                ])
                .unwrap();
        let ta = ta_builder.build();
        let lia =
            taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton::try_from(
                ta.clone(),
            )
            .unwrap();

        let mut interval_tas = IntervalTABuilder::new(lia, SMTSolverBuilder::default(), vec![])
            .build()
            .unwrap();
        let interval_threshold_automaton = interval_tas.next().unwrap();
        let nxt = interval_tas.next();
        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());

        interval_threshold_automaton
    }

    #[test]
    fn test_location_variables() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_automaton();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let var_mgr = builder.cs.bdd_mgr;
        assert!(var_mgr.get_location_var(&Location::new("v0")).is_ok());
        assert!(
            var_mgr
                .get_primed_location_var(&Location::new("v0"))
                .is_ok()
        );
        assert!(var_mgr.get_location_var(&Location::new("unknown")).is_err());
        assert!(
            !var_mgr
                .get_location_var(&Location::new("v0"))
                .unwrap()
                .eq(var_mgr
                    .get_primed_location_var(&Location::new("v0"))
                    .unwrap())
        );
    }

    #[test]
    fn test_create_shared_variables() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_automaton();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);

        // I_0 = [0,1)
        let interval_0 = Interval::zero();
        // I_1 = [1,n-t)
        let interval_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );
        // I_2 = [n-t,infty)
        let interval_2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        let interval_0_x0_bdd = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_0);
        let interval_1_x0_bdd = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_1);
        let interval_2_x0_bdd = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_2);

        assert!(interval_0_x0_bdd.is_ok());
        assert!(interval_1_x0_bdd.is_ok());
        assert!(interval_2_x0_bdd.is_ok());

        // x0_0 = !(i_0 | i_2)
        let x0_0 = (interval_0_x0_bdd
            .clone()
            .unwrap()
            .or(interval_2_x0_bdd.clone().unwrap()))
        .not();
        // x0_1 = !(i_0 | i_1)
        let x0_1 = (interval_0_x0_bdd
            .clone()
            .unwrap()
            .or(interval_1_x0_bdd.clone().unwrap()))
        .not();

        assert!(
            interval_0_x0_bdd
                .unwrap()
                .eq(&(x0_0.not().and(&x0_1.not())))
        );
        assert!(
            interval_1_x0_bdd
                .clone()
                .unwrap()
                .eq(&(x0_0.and(&x0_1.not())))
        );
        assert!(interval_2_x0_bdd.unwrap().eq(&(x0_0.not().and(&x0_1))));

        let interval_1_x0_primed_bdd = builder
            .cs
            .bdd_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x0"), &interval_1);
        assert!(interval_1_x0_primed_bdd.is_ok());
        assert!(
            !interval_1_x0_primed_bdd
                .unwrap()
                .eq(interval_1_x0_bdd.unwrap())
        );

        assert!(
            builder
                .cs
                .bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                .is_ok()
        );
        assert!(
            builder
                .cs
                .bdd_mgr
                .get_primed_shared_interval_bdd(&Variable::new("x1"), &interval_0)
                .is_ok()
        );
    }

    #[test]
    fn test_build_initial_states() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_automaton();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        let initial_states_bdd = builder.build_initial_states().set_of_states;

        //locations
        let wait = builder.cs.bdd_mgr.get_location_var(&Location::new("wait"));
        let d_0 = builder.cs.bdd_mgr.get_location_var(&Location::new("d0"));
        let d_1 = builder.cs.bdd_mgr.get_location_var(&Location::new("d1"));
        assert!(wait.is_ok());
        assert!(d_0.is_ok());
        assert!(d_1.is_ok());
        let mut correct_initial_states_bdd = wait
            .unwrap()
            .not()
            .and(&(d_0.unwrap().not().and(&d_1.unwrap().not())));

        //intervals
        // I_0 = [0,1)
        let interval_0 = Interval::zero();
        let interval_0_x0_bdd = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_0);
        let interval_0_x1_bdd = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x1"), &interval_0);
        assert!(interval_0_x0_bdd.is_ok());
        assert!(interval_0_x1_bdd.is_ok());
        let interval_0_x0_bdd = interval_0_x0_bdd.unwrap();
        let interval_0_x1_bdd = interval_0_x1_bdd.unwrap();

        // I_1 = [1,n-t)
        let interval_1_nt = Interval::new(
            IntervalBoundary::from_const(1),
            false,
            IntervalBoundary::new_bound(
                WeightedSum::new([
                    (Parameter::new("n"), Fraction::from(1)),
                    (Parameter::new("t"), -Fraction::from(1)),
                ]),
                0,
            ),
            true,
        );
        let interval_1_nt_x0 = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_1_nt);
        let interval_1_nt_x1 = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x1"), &interval_1_nt);
        assert!(interval_1_nt_x0.is_ok());
        assert!(interval_1_nt_x1.is_ok());
        let interval_1_nt_x0 = interval_1_nt_x0.unwrap();
        let interval_1_nt_x1 = interval_1_nt_x1.unwrap();

        // I_2 = [n-t, infty)
        let interval_nt_inf = Interval::new(
            IntervalBoundary::new_bound(
                WeightedSum::new([
                    (Parameter::new("n"), Fraction::from(1)),
                    (Parameter::new("t"), -Fraction::from(1)),
                ]),
                0,
            ),
            false,
            IntervalBoundary::new_infty(),
            true,
        );
        let interval_nt_inf_x0 = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_nt_inf);
        let interval_nt_inf_x1 = builder
            .cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x1"), &interval_nt_inf);
        assert!(interval_nt_inf_x0.is_ok());
        assert!(interval_nt_inf_x1.is_ok());
        let interval_nt_inf_x0 = interval_nt_inf_x0.unwrap();
        let interval_nt_inf_x1 = interval_nt_inf_x1.unwrap();

        let init_intervals_x0 = interval_0_x0_bdd
            .or(interval_1_nt_x0)
            .or(interval_nt_inf_x0);
        let init_intervals_x1 = interval_0_x1_bdd
            .or(interval_1_nt_x1)
            .or(interval_nt_inf_x1);

        correct_initial_states_bdd =
            correct_initial_states_bdd.and(&init_intervals_x0.and(&init_intervals_x1));

        assert!(initial_states_bdd.eq(&correct_initial_states_bdd));
    }

    #[test]
    fn test_build_symbolic_transitions() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_automaton();
        let builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);

        let transitions = builder.build_symbolic_transitions();

        assert_eq!(transitions.len(), 4);

        let var_mgr = builder.cs.bdd_mgr;

        // r0: v0 -> wait, guard: true, action: x0 = x0 + 1

        // locations
        // `from`(v0) and `to_prime` (wait')
        let mut correct_r0 = var_mgr
            .get_location_var(&Location::new("v0"))
            .unwrap()
            .clone();
        correct_r0 = correct_r0.and(
            var_mgr
                .get_primed_location_var(&Location::new("wait"))
                .unwrap(),
        );
        // v1 = v1', d0 = d0', d1 = d1'
        correct_r0 = correct_r0.and(
            &(var_mgr
                .get_location_var(&Location::new("v1"))
                .unwrap()
                .equiv(
                    var_mgr
                        .get_primed_location_var(&Location::new("v1"))
                        .unwrap(),
                )),
        );
        correct_r0 = correct_r0.and(
            &(var_mgr
                .get_location_var(&Location::new("d0"))
                .unwrap()
                .equiv(
                    var_mgr
                        .get_primed_location_var(&Location::new("d0"))
                        .unwrap(),
                )),
        );
        correct_r0 = correct_r0.and(
            &(var_mgr
                .get_location_var(&Location::new("d1"))
                .unwrap()
                .equiv(
                    var_mgr
                        .get_primed_location_var(&Location::new("d1"))
                        .unwrap(),
                )),
        );

        // intervals for update
        // I_0 = [0,1)
        let interval_0 = Interval::zero();
        // I_1 = [1,n-t)
        let interval_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );
        // I_2 = [n-t,infty)
        let interval_2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        let interval_0_x0_bdd = var_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_0)
            .unwrap();
        let interval_1_x0_bdd = var_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_1)
            .unwrap();
        let interval_2_x0_bdd = var_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_2)
            .unwrap();
        let interval_1_x0_prime_bdd = var_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x0"), &interval_1)
            .unwrap();
        let interval_2_x0_prime_bdd = var_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x0"), &interval_2)
            .unwrap();

        // I_0 => I_1'
        correct_r0 = correct_r0.and(&(interval_0_x0_bdd.implies(interval_1_x0_prime_bdd)));
        // I_1 => I_1' | I_2'
        correct_r0 = correct_r0.and(
            &(interval_1_x0_bdd.implies(&(interval_1_x0_prime_bdd.or(interval_2_x0_prime_bdd)))),
        );
        // I_2 => I_2'
        correct_r0 = correct_r0.and(&(interval_2_x0_bdd.implies(interval_2_x0_prime_bdd)));

        // for x_1 intervals unchanged
        correct_r0 = correct_r0.and(
            &var_mgr
                .get_unchanged_interval_bdd(&Variable::new("x1"))
                .unwrap(),
        );

        // rule_id
        for t in &transitions {
            if t.abstract_rule().id() == 0 {
                correct_r0 = correct_r0.and(var_mgr.get_rule_bdd(t.abstract_rule()).unwrap());
            }
        }

        // r3: wait -> d1, guard: x1 >= n - t, action: none

        // locations
        // `from`(wait) and `to_prime` (d1')
        let mut correct_r3 = var_mgr
            .get_location_var(&Location::new("wait"))
            .unwrap()
            .clone();
        correct_r3 = correct_r3.and(
            var_mgr
                .get_primed_location_var(&Location::new("d1"))
                .unwrap(),
        );
        // v0 = v0', v1 = v1', d0 = d0'
        correct_r3 = correct_r3.and(
            &(var_mgr
                .get_location_var(&Location::new("v0"))
                .unwrap()
                .equiv(
                    var_mgr
                        .get_primed_location_var(&Location::new("v0"))
                        .unwrap(),
                )),
        );
        correct_r3 = correct_r3.and(
            &(var_mgr
                .get_location_var(&Location::new("v1"))
                .unwrap()
                .equiv(
                    var_mgr
                        .get_primed_location_var(&Location::new("v1"))
                        .unwrap(),
                )),
        );
        correct_r3 = correct_r3.and(
            &(var_mgr
                .get_location_var(&Location::new("d0"))
                .unwrap()
                .equiv(
                    var_mgr
                        .get_primed_location_var(&Location::new("d0"))
                        .unwrap(),
                )),
        );

        // for x_0 intervals unchanged
        correct_r3 = correct_r3.and(
            &var_mgr
                .get_unchanged_interval_bdd(&Variable::new("x0"))
                .unwrap(),
        );

        // for x_1 intervals unchanged
        correct_r3 = correct_r3.and(
            &var_mgr
                .get_unchanged_interval_bdd(&Variable::new("x1"))
                .unwrap(),
        );

        // rule_id
        for t in &transitions {
            if t.abstract_rule().id() == 3 {
                correct_r3 = correct_r3.and(var_mgr.get_rule_bdd(t.abstract_rule()).unwrap());
            }
        }

        // guard: x1 has to be in I_2
        correct_r3 = correct_r3.and(
            var_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                .unwrap(),
        );

        for t in transitions {
            assert!(t.abstract_rule().id() < 4);
            if t.abstract_rule().id() == 0 {
                assert!(correct_r0.eq(&t.transition_bdd));
            }
            if t.abstract_rule().id() == 3 {
                assert!(correct_r3.eq(&t.transition_bdd));
            }
        }
    }

    #[test]
    fn test_build_symbolic_transition_relation() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_automaton();
        let mut builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        builder.initialize();

        assert!(
            builder
                .cs
                .transition_relation
                .and(&builder.cs.transitions[1].transition_bdd)
                .satisfiable()
        );
        assert!(
            builder
                .cs
                .transition_relation
                .and(
                    builder
                        .cs
                        .bdd_mgr
                        .get_rule_bdd(builder.cs.transitions[1].abstract_rule())
                        .unwrap()
                )
                .satisfiable()
        );
        assert!(
            builder
                .cs
                .transition_relation
                .and(&builder.cs.transitions[2].transition_bdd)
                .satisfiable()
        );
        assert!(
            builder
                .cs
                .transition_relation
                .and(
                    builder
                        .cs
                        .bdd_mgr
                        .get_rule_bdd(builder.cs.transitions[2].abstract_rule())
                        .unwrap()
                )
                .satisfiable()
        );
    }

    #[test]
    fn test_decrement_transition() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_dec_reset_automaton();

        let mut builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        builder.initialize();

        assert_eq!(builder.cs.transitions.len(), 2);

        let var_mgr = builder.cs.bdd_mgr;

        // r0: l0 -> l1, guard: true, action: x = x - 1

        // locations
        // `from`(l0) and `to_prime` (l1')
        let mut correct_r0 = var_mgr
            .get_location_var(&Location::new("l0"))
            .unwrap()
            .clone();
        correct_r0 = correct_r0.and(
            var_mgr
                .get_primed_location_var(&Location::new("l1"))
                .unwrap(),
        );

        // intervals for update
        // I_0 = [0,1)
        let interval_0 = Interval::zero();
        // I_1 = [1,n-t)
        let interval_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            true,
        );
        // I_2 = [n-t,infty)
        let interval_2 = Interval::new(
            IntervalBoundary::Bound(Threshold::new(
                [
                    (Parameter::new("n"), 1.into()),
                    (Parameter::new("t"), Fraction::new(1, 1, true)),
                ],
                0,
            )),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        let interval_0_bdd = var_mgr
            .get_shared_interval_bdd(&Variable::new("x"), &interval_0)
            .unwrap();
        let interval_1_bdd = var_mgr
            .get_shared_interval_bdd(&Variable::new("x"), &interval_1)
            .unwrap();
        let interval_2_bdd = var_mgr
            .get_shared_interval_bdd(&Variable::new("x"), &interval_2)
            .unwrap();
        let interval_0_prime_bdd = var_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x"), &interval_0)
            .unwrap();
        let interval_1_prime_bdd = var_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x"), &interval_1)
            .unwrap();
        let interval_2_prime_bdd = var_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x"), &interval_2)
            .unwrap();

        // I_0 => I_0'
        correct_r0 = correct_r0.and(&(interval_0_bdd.implies(interval_0_prime_bdd)));
        // I_1 => I_1' | I_0'
        correct_r0 = correct_r0
            .and(&(interval_1_bdd.implies(&(interval_1_prime_bdd.or(interval_0_prime_bdd)))));
        // I_2 => I_2' | I_1'
        correct_r0 = correct_r0
            .and(&(interval_2_bdd.implies(&(interval_2_prime_bdd.or(interval_1_prime_bdd)))));

        // rule_id
        for t in &builder.cs.transitions {
            if t.abstract_rule.id() == 0 {
                correct_r0 = correct_r0.and(var_mgr.get_rule_bdd(t.abstract_rule()).unwrap());
                assert!(correct_r0.eq(&t.transition_bdd));
            }
        }
    }

    #[test]
    fn test_reset_transition() {
        let mgr = taco_bdd::BDDManager::default();
        let ata = test_dec_reset_automaton();

        let mut builder: ZCSBuilder = ZCSBuilder::new(&mgr, &ata);
        builder.initialize();

        assert_eq!(builder.cs.transitions.len(), 2);

        let var_mgr = builder.cs.bdd_mgr;

        // r1: l0 -> l1, guard: true, action: x = 0

        // locations
        // `from`(l0) and `to_prime` (l1')
        let mut correct_r1 = var_mgr
            .get_location_var(&Location::new("l0"))
            .unwrap()
            .clone();
        correct_r1 = correct_r1.and(
            var_mgr
                .get_primed_location_var(&Location::new("l1"))
                .unwrap(),
        );

        // intervals for update
        // I_0 = [0,1)
        let interval_0 = Interval::zero();

        let interval_0_prime_bdd = var_mgr
            .get_primed_shared_interval_bdd(&Variable::new("x"), &interval_0)
            .unwrap();

        // I_0'
        correct_r1 = correct_r1.and(interval_0_prime_bdd);

        // rule_id
        for t in &builder.cs.transitions {
            if t.abstract_rule().id() == 1 {
                correct_r1 = correct_r1.and(var_mgr.get_rule_bdd(t.abstract_rule()).unwrap());
                assert!(correct_r1.eq(&t.transition_bdd));
            }
        }
    }
}

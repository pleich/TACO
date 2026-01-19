//! This module contains the symbolic representation
//! of a 01-CS (ZCS) for a given IntervalThresholdAutomaton.

pub mod builder;

use bdd_var_manager::BddVarManager;
use taco_bdd::BDD;
use taco_bdd::Bdd;
use taco_interval_ta::IntervalTARule;
use taco_interval_ta::IntervalThresholdAutomaton;
use taco_interval_ta::interval::Interval;
use taco_threshold_automaton::ThresholdAutomaton;
use taco_threshold_automaton::expressions::{Location, Variable};

use crate::paths::VariableAssignment;

mod bdd_var_manager;

/// Type representing a symbolic 01-CS (ZCS)
#[derive(Debug, Clone)]
pub struct ZCS<'a> {
    /// bdd manager to perform all bdd operations
    bdd_mgr: BddVarManager,
    /// underlying abstract threshold automaton
    ata: &'a IntervalThresholdAutomaton,
    /// initial states of the 01-CS (ZCS)
    initial_states: ZCSStates,
    /// set of transitions of the 01-CS (ZCS)
    transitions: Vec<SymbolicTransition>,
    /// transition relation of the 01-CS (ZCS) as a single bdd
    transition_relation: BDD,
}
impl ZCS<'_> {
    /// Computes the set of successors for a symbolic state `from`
    /// rule_ids for `with` are not abstracted
    pub fn compute_successor(&self, from: ZCSStates, with: SymbolicTransition) -> ZCSStates {
        // intersect transition `with` with symbolic state `from`
        let mut succ = from.set_of_states.and(&with.transition_bdd);
        // abstract unprimed variables
        succ = self.bdd_mgr.exists_unprimed(&succ);
        // unprime all bdd variables in `succ`
        succ = self.bdd_mgr.swap_unprimed_primed_bdd_vars(&succ);

        ZCSStates {
            set_of_states: succ,
        }
    }

    /// Computes the set of predecessors for a symbolic state `to`
    /// Bdd variables for rule_ids are not abstracted
    pub fn compute_predecessor(&self, to: ZCSStates) -> ZCSStates {
        // prime all bdd variables in `to`
        let primed_to = self
            .bdd_mgr
            .swap_unprimed_primed_bdd_vars(&to.set_of_states);
        // intersect with transition relation
        let mut pred = primed_to.and(&self.transition_relation);
        // abstract primed variables
        pred = self.bdd_mgr.exists_primed(&pred);
        ZCSStates {
            set_of_states: pred,
        }
    }

    /// returns a new empty set of states
    pub fn new_empty_sym_state(&self) -> ZCSStates {
        ZCSStates {
            set_of_states: self.bdd_mgr.get_bdd_false(),
        }
    }

    /// returns a new "full" set of states
    pub fn new_full_sym_state(&self) -> ZCSStates {
        ZCSStates {
            set_of_states: self.bdd_mgr.get_bdd_true(),
        }
    }

    /// returns the set of states where a given location is occupied
    pub fn get_sym_state_for_loc(&self, loc: &Location) -> ZCSStates {
        ZCSStates {
            set_of_states: self
                .bdd_mgr
                .get_location_var(loc)
                .expect("failed to get location bdd")
                .clone(),
        }
    }

    /// returns the set of states where a given shared variable is in the given 'interval'
    pub fn get_sym_state_for_shared_interval(
        &self,
        shared: &Variable,
        interval: &Interval,
    ) -> ZCSStates {
        ZCSStates {
            set_of_states: self
                .bdd_mgr
                .get_shared_interval_bdd(shared, interval)
                .expect("failed to get shared interval bdd")
                .clone(),
        }
    }

    /// returns the set of states where the rule_id of a given 'rule' is applied
    pub fn get_sym_state_for_rule(&self, rule: &IntervalTARule) -> ZCSStates {
        ZCSStates {
            set_of_states: self
                .bdd_mgr
                .get_rule_bdd(rule)
                .expect("failed to get rule bdd")
                .clone(),
        }
    }

    /// returns the symbolic states that abstracts rule_ids from 'states'
    pub fn abstract_rule_vars(&self, states: ZCSStates) -> ZCSStates {
        ZCSStates {
            set_of_states: self.bdd_mgr.exists_rule_vars(&states.set_of_states),
        }
    }

    /// set of initial states of the 01-CS (ZCS)
    pub fn initial_states(&self) -> ZCSStates {
        self.initial_states.clone()
    }

    /// returns an iterator over the encoded transition rules
    pub fn transitions(&self) -> impl Iterator<Item = &SymbolicTransition> {
        self.transitions.iter()
    }

    /// returns an iterator over the locations of the underlying threshold automaton
    pub fn locations(&self) -> impl Iterator<Item = &Location> {
        self.ata.locations()
    }

    /// returns an iterator over the shared variables of the underlying threshold automaton
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.ata.variables()
    }

    /// returns an iterator over the ordered intervals for a given shared variable
    pub fn get_ordered_intervals_for_shared(&self, shared: &Variable) -> &Vec<Interval> {
        self.ata
            .get_ordered_intervals(shared)
            .expect("failed to get ordered intervals for shared variable")
    }

    /// returns the symbolic variable assignment for a given variable assignment
    pub fn get_sym_var_assignment(&self, assign: VariableAssignment) -> SymbolicVariableAssignment {
        let mut assign_bdd = self.bdd_mgr.get_bdd_true();
        for (shared, interval) in assign.assignments() {
            let interval_bdd = self
                .bdd_mgr
                .get_shared_interval_bdd(shared, interval)
                .expect("failed to get shared interval bdd");
            assign_bdd = assign_bdd.and(interval_bdd);
        }
        SymbolicVariableAssignment::new(assign_bdd, assign)
    }

    /// returns if the underlying threshold automaton contains any decrementing rules
    pub fn has_decrements(&self) -> bool {
        self.ata.has_decrements()
    }
}

/// Type to represent a set of states in the 01-CS (ZCS)
#[derive(Debug, Clone, PartialEq)]
pub struct ZCSStates {
    /// bdd to represent a set of states
    set_of_states: BDD,
}
impl ZCSStates {
    /// creates a new 'ZCSStates'
    pub fn new(node: BDD) -> Self {
        ZCSStates {
            set_of_states: node,
        }
    }
    /// returns the underlying set_of_states
    pub fn set_of_states(&self) -> &BDD {
        &self.set_of_states
    }

    /// performs the `intersection` operation
    pub fn intersection(&self, states: &ZCSStates) -> ZCSStates {
        ZCSStates {
            set_of_states: self.set_of_states.and(&states.set_of_states),
        }
    }

    /// checks if the symbolic state contains a given symbolic variable assignment
    pub fn contains_sym_assignment(&self, sym_assignment: &SymbolicVariableAssignment) -> bool {
        self.set_of_states
            .and(&sym_assignment.assignment_bdd)
            .satisfiable()
    }

    /// performs the intersection of a symbolic_states and a symbolic variable assignment
    pub fn intersect_assignment(&self, sym_assignment: &SymbolicVariableAssignment) -> ZCSStates {
        ZCSStates {
            set_of_states: self.set_of_states.and(&sym_assignment.assignment_bdd),
        }
    }

    /// performs the restriction of a symbolic_states and a symbolic variable assignment
    ///
    /// i.e., removes all states that satisfy the variable assignment
    pub fn remove_assignment(&self, sym_assignment: &SymbolicVariableAssignment) -> ZCSStates {
        ZCSStates {
            set_of_states: self
                .set_of_states
                .and(&!sym_assignment.assignment_bdd.clone()),
        }
    }

    /// performs the `union` operation
    pub fn union(&self, states: &ZCSStates) -> ZCSStates {
        ZCSStates {
            set_of_states: self.set_of_states.or(&states.set_of_states),
        }
    }

    /// returns the complement
    pub fn complement(&self) -> ZCSStates {
        ZCSStates {
            set_of_states: self.set_of_states.not(),
        }
    }
    /// checks if the set of states is empty
    pub fn is_empty(&self) -> bool {
        !self.set_of_states.satisfiable()
    }

    /// checks if two SymbolicStates are equal
    pub fn equal(&self, other: &ZCSStates) -> bool {
        self.set_of_states.eq(&other.set_of_states)
    }
}

/// Type to represent a symbolic transition in the 01-CS (ZCS)
#[derive(Debug, Clone, PartialEq)]
pub struct SymbolicTransition {
    /// underlying rule of the TA
    abstract_rule: IntervalTARule,
    /// bdd to represent all possible transitions of the 01-CS (ZCS)
    /// based on the underlying rule of the TA
    transition_bdd: BDD,
}
impl SymbolicTransition {
    /// Creates a new `SymbolicTransition`.
    pub fn new(node: BDD, transition: IntervalTARule) -> Self {
        SymbolicTransition {
            abstract_rule: transition,
            transition_bdd: node,
        }
    }
    /// return the underlying abstract rule
    pub fn abstract_rule(&self) -> &IntervalTARule {
        &self.abstract_rule
    }
}

/// Type that represents a symbolic variable assignment
#[derive(Debug, Clone)]
pub struct SymbolicVariableAssignment {
    /// bdd representation of the variable assignment
    assignment_bdd: BDD,
    /// concrete variable assignment
    assignment: VariableAssignment,
}
impl SymbolicVariableAssignment {
    /// creates a new 'SymbolicVariableAssignment'
    pub fn new(assignment_bdd: BDD, assignment: VariableAssignment) -> Self {
        SymbolicVariableAssignment {
            assignment_bdd,
            assignment,
        }
    }

    /// returns the bdd representation of the variable assignment
    pub fn assignment_bdd(&self) -> &BDD {
        &self.assignment_bdd
    }

    /// returns the concrete variable assignment
    pub fn assignment(&self) -> &VariableAssignment {
        &self.assignment
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use builder::ZCSBuilder;
    use taco_bdd::Bdd;
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
        BooleanVarConstraint, LocationConstraint, ParameterConstraint, RuleDefinition,
    };
    use taco_threshold_automaton::{
        expressions::{ComparisonOp, IntegerExpression, Parameter},
        general_threshold_automaton::{Action, builder::RuleBuilder},
    };

    /// Constructs the 01-CS for the abstract threshold automaton in `symbolic-01-cs/src/builder` constructed in `test_automaton()`
    fn get_ata() -> IntervalThresholdAutomaton {
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
                .with_initial_variable_constraints([
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x0"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ]
                ).unwrap()
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
        interval_tas.next().unwrap()
    }

    #[test]
    fn test_compute_successor_update() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        // initial_states: ((-,-,0,0,0),(I_0,I_0))
        let mut t_0: Option<&SymbolicTransition> = None;
        for t in &cs.transitions {
            if t.abstract_rule().id() == 0 {
                t_0 = Some(t);
            }
        }
        assert!(t_0.is_some());
        let succ = cs.compute_successor(cs.initial_states.clone(), t_0.unwrap().clone());

        let wait = cs.bdd_mgr.get_location_var(&Location::new("wait")).unwrap();
        let d0 = cs.bdd_mgr.get_location_var(&Location::new("d0")).unwrap();
        let d1 = cs.bdd_mgr.get_location_var(&Location::new("d1")).unwrap();

        // succ = initial_states -> rule_0 = ((-,-,1,0,0),({I_0,I_1}, I_0)) & r_0_ids
        let mut correct_succ = wait.and(&d0.not()).and(&d1.not());
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
        correct_succ = correct_succ.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x0"), &interval_1)
                .unwrap(),
        );
        correct_succ = correct_succ.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_0)
                .unwrap(),
        );

        correct_succ = correct_succ.and(
            cs.bdd_mgr
                .get_rule_bdd(t_0.unwrap().abstract_rule())
                .unwrap(),
        );
        assert!(correct_succ.eq(&succ.set_of_states));
    }

    #[test]
    fn test_compute_successor_guard() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        // from = ((-,-,-,0,-),(I_2,-))
        let mut from = cs
            .bdd_mgr
            .get_location_var(&Location::new("d0"))
            .unwrap()
            .not();
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
        from = from.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x0"), &interval_2)
                .unwrap(),
        );

        let mut t_3: Option<&SymbolicTransition> = None;
        for t in &cs.transitions {
            if t.abstract_rule().id() == 3 {
                t_3 = Some(t);
            }
        }
        assert!(t_3.is_some());

        // succ = from -> rule_3 = ((-,-,-,0,1),(I_2, I_2)) & r_3_ids
        let succ = cs.compute_successor(
            ZCSStates {
                set_of_states: from,
            },
            t_3.unwrap().clone(),
        );

        let mut correct_succ = cs
            .bdd_mgr
            .get_location_var(&Location::new("d0"))
            .unwrap()
            .not();
        correct_succ = correct_succ.and(cs.bdd_mgr.get_location_var(&Location::new("d1")).unwrap());

        correct_succ = correct_succ.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x0"), &interval_2)
                .unwrap(),
        );
        correct_succ = correct_succ.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                .unwrap(),
        );

        correct_succ = correct_succ.and(
            cs.bdd_mgr
                .get_rule_bdd(t_3.unwrap().abstract_rule())
                .unwrap(),
        );

        assert!(correct_succ.eq(&succ.set_of_states));
    }

    #[test]
    fn test_compute_predecessor_update() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        // to = ((0,0,1,-,0),(I_1,I_2)
        let v0 = cs.bdd_mgr.get_location_var(&Location::new("v0")).unwrap();
        let v1 = cs.bdd_mgr.get_location_var(&Location::new("v1")).unwrap();
        let wait = cs.bdd_mgr.get_location_var(&Location::new("wait")).unwrap();
        let d1 = cs.bdd_mgr.get_location_var(&Location::new("d1")).unwrap();
        let mut to = v0.not().and(&v1.not()).and(wait).and(&d1.not());
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
        to = to.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x0"), &interval_1)
                .unwrap(),
        );
        to = to.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                .unwrap(),
        );

        let from = cs.compute_predecessor(ZCSStates {
            set_of_states: to.clone(),
        });

        let mut t_0: Option<&SymbolicTransition> = None;
        let mut t_1: Option<&SymbolicTransition> = None;
        for t in &cs.transitions {
            if t.abstract_rule().id() == 0 {
                t_0 = Some(t);
            }
            if t.abstract_rule().id() == 1 {
                t_1 = Some(t);
            }
        }
        assert!(t_0.is_some());
        assert!(t_1.is_some());

        // from = ((1,0,-,-,0),({I_0,I_1},I_2)) & rule_0_ids (or no valid interval for x0)
        //      | ((0,1,-,-,0),(I_1,{I_1,I_2})) & rule_1_ids (or no valid interval for x1)

        let mut correct_from_0 = v0.and(&v1.not()).and(&d1.not());
        let x_0_interval_0 = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_0)
            .unwrap();
        let x_0_interval_1 = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_1)
            .unwrap();
        let x_0_interval_2 = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_2)
            .unwrap();
        let invalid_interval_x_0 = x_0_interval_0
            .not()
            .and(&x_0_interval_1.not())
            .and(&x_0_interval_2.not());
        correct_from_0 =
            correct_from_0.and(&(invalid_interval_x_0.or(x_0_interval_0).or(x_0_interval_1)));
        correct_from_0 = correct_from_0.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                .unwrap(),
        );
        correct_from_0 = correct_from_0.and(
            cs.bdd_mgr
                .get_rule_bdd(t_0.unwrap().abstract_rule())
                .unwrap(),
        );

        let mut correct_from_1 = v1.and(&v0.not()).and(&d1.not());
        let x_1_interval_0 = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x1"), &interval_0)
            .unwrap();
        let x_1_interval_1 = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x1"), &interval_1)
            .unwrap();
        let x_1_interval_2 = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
            .unwrap();
        let invalid_interval_x_1 = x_1_interval_0
            .not()
            .and(&x_1_interval_1.not())
            .and(&x_1_interval_2.not());
        correct_from_1 =
            correct_from_1.and(&(invalid_interval_x_1.or(x_1_interval_1).or(x_1_interval_2)));
        correct_from_1 = correct_from_1.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x0"), &interval_1)
                .unwrap(),
        );
        correct_from_1 = correct_from_1.and(
            cs.bdd_mgr
                .get_rule_bdd(t_1.unwrap().abstract_rule())
                .unwrap(),
        );

        assert!((correct_from_0.or(&correct_from_1)).eq(&from.set_of_states));
    }

    #[test]
    fn test_compute_predecessor_guard() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        // to = ((0,-,0,1,1),(-,-)
        let v0 = cs.bdd_mgr.get_location_var(&Location::new("v0")).unwrap();
        let wait = cs.bdd_mgr.get_location_var(&Location::new("wait")).unwrap();
        let d0 = cs.bdd_mgr.get_location_var(&Location::new("d0")).unwrap();
        let d1 = cs.bdd_mgr.get_location_var(&Location::new("d1")).unwrap();
        let to = v0.not().and(&wait.not()).and(d0).and(d1);
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

        let from = cs.compute_predecessor(ZCSStates { set_of_states: to });

        let mut t_2: Option<&SymbolicTransition> = None;
        let mut t_3: Option<&SymbolicTransition> = None;
        for t in &cs.transitions {
            if t.abstract_rule().id() == 2 {
                t_2 = Some(t);
            }
            if t.abstract_rule().id() == 3 {
                t_3 = Some(t);
            }
        }
        assert!(t_2.is_some());
        assert!(t_3.is_some());

        // from = ((0,-,1,-,1),(I_2,-)) & rule_2_ids
        //      | ((0,-,1,1,-),(-,I_2)) & rule_3_ids
        let mut correct_from_2 = v0.not().and(wait).and(d1);
        correct_from_2 = correct_from_2.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x0"), &interval_2)
                .unwrap(),
        );
        correct_from_2 = correct_from_2.and(
            cs.bdd_mgr
                .get_rule_bdd(&t_2.unwrap().abstract_rule.clone())
                .unwrap(),
        );

        let mut correct_from_3 = v0.not().and(wait).and(d0);
        correct_from_3 = correct_from_3.and(
            cs.bdd_mgr
                .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                .unwrap(),
        );
        correct_from_3 = correct_from_3.and(
            cs.bdd_mgr
                .get_rule_bdd(&t_3.unwrap().abstract_rule.clone())
                .unwrap(),
        );

        assert!((correct_from_2.or(&correct_from_3)).eq(&from.set_of_states));
    }

    #[test]
    fn test_locations() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let locs: Vec<Location> = cs.locations().cloned().collect();
        assert_eq!(locs.len(), 5);
        assert!(locs.contains(&Location::new("v0")));
        assert!(locs.contains(&Location::new("v1")));
        assert!(locs.contains(&Location::new("wait")));
        assert!(locs.contains(&Location::new("d0")));
        assert!(locs.contains(&Location::new("d1")));
    }

    #[test]
    fn test_variables() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let vars: Vec<Variable> = cs.variables().cloned().collect();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Variable::new("x0")));
        assert!(vars.contains(&Variable::new("x1")));
    }

    #[test]
    fn test_get_ordered_intervals_for_shared_variable() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let intervals_x0 = cs.get_ordered_intervals_for_shared(&Variable::new("x0"));
        let intervals_x1 = cs.get_ordered_intervals_for_shared(&Variable::new("x1"));

        assert_eq!(intervals_x0.len(), 3);
        assert_eq!(intervals_x1.len(), 3);

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

        assert_eq!(intervals_x0[0], interval_0);
        assert_eq!(intervals_x0[1], interval_1);
        assert_eq!(intervals_x0[2], interval_2);

        assert_eq!(intervals_x1[0], interval_0);
        assert_eq!(intervals_x1[1], interval_1);
        assert_eq!(intervals_x1[2], interval_2);
    }

    #[test]
    fn test_get_sym_var_assignment() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let mut var_assign = VariableAssignment::new();
        // x0 in I_1
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
        let _ = var_assign.add_shared_var_interval(Variable::new("x0"), interval_1.clone());
        // x1 in I_2
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
        let _ = var_assign.add_shared_var_interval(Variable::new("x1"), interval_2.clone());

        let sym_var_assign = cs.get_sym_var_assignment(var_assign.clone());

        let correct_bdd = cs
            .bdd_mgr
            .get_shared_interval_bdd(&Variable::new("x0"), &interval_1)
            .unwrap()
            .and(
                cs.bdd_mgr
                    .get_shared_interval_bdd(&Variable::new("x1"), &interval_2)
                    .unwrap(),
            );

        assert!(correct_bdd.eq(sym_var_assign.assignment_bdd()));
        let assign = sym_var_assign.assignment();
        let assignments: Vec<(&Variable, &Interval)> = assign.assignments().collect();
        assert_eq!(assignments.len(), 2);
        assert!(assignments.contains(&(&Variable::new("x0"), &interval_1)));
        assert!(assignments.contains(&(&Variable::new("x1"), &interval_2)));
    }

    #[test]
    fn test_contains_sym_assignment() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let initial_states = cs.initial_states();

        let mut var_assign = VariableAssignment::new();
        // x0 in I_0
        let interval_0 = Interval::zero();
        let _ = var_assign.add_shared_var_interval(Variable::new("x0"), interval_0.clone());
        // x1 in I_0
        let _ = var_assign.add_shared_var_interval(Variable::new("x1"), interval_0.clone());

        let sym_var_assign = cs.get_sym_var_assignment(var_assign.clone());

        assert!(initial_states.contains_sym_assignment(&sym_var_assign));

        let mut var_assign2 = VariableAssignment::new();
        // x0 in I_1
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
        let _ = var_assign2.add_shared_var_interval(Variable::new("x0"), interval_1.clone());
        // x1 in I_0
        let _ = var_assign2.add_shared_var_interval(Variable::new("x1"), interval_0.clone());

        let sym_var_assign2 = cs.get_sym_var_assignment(var_assign2.clone());

        assert!(!initial_states.contains_sym_assignment(&sym_var_assign2));
    }

    #[test]
    fn test_intersect_assignment() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let initial_states = cs.initial_states();

        let mut var_assign = VariableAssignment::new();
        // x0 in I_0
        let interval_0 = Interval::zero();
        let _ = var_assign.add_shared_var_interval(Variable::new("x0"), interval_0.clone());
        // x1 in I_0
        let _ = var_assign.add_shared_var_interval(Variable::new("x1"), interval_0.clone());

        let sym_var_assign = cs.get_sym_var_assignment(var_assign.clone());

        let intersected = initial_states.intersect_assignment(&sym_var_assign);
        assert!(intersected.equal(&initial_states));

        let mut var_assign2 = VariableAssignment::new();
        // x0 in I_1
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
        let _ = var_assign2.add_shared_var_interval(Variable::new("x0"), interval_1.clone());
        // x1 in I_0
        let _ = var_assign2.add_shared_var_interval(Variable::new("x1"), interval_0.clone());

        let sym_var_assign2 = cs.get_sym_var_assignment(var_assign2.clone());

        let intersected2 = initial_states.intersect_assignment(&sym_var_assign2);
        assert!(intersected2.is_empty());

        let changed_initial_states = initial_states.union(&ZCSStates {
            set_of_states: sym_var_assign2.assignment_bdd().clone(),
        });
        let intersected3 = changed_initial_states.intersect_assignment(&sym_var_assign2);
        assert!(intersected3.equal(&ZCSStates {
            set_of_states: sym_var_assign2.assignment_bdd().clone()
        }));

        let intersected4 = changed_initial_states.intersect_assignment(&sym_var_assign);
        assert!(intersected4.equal(&initial_states));
    }

    #[test]
    fn test_remove_assignment() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let initial_states = cs.initial_states();

        let mut var_assign = VariableAssignment::new();
        // x0 in I_0
        let interval_0 = Interval::zero();
        let _ = var_assign.add_shared_var_interval(Variable::new("x0"), interval_0.clone());
        // x1 in I_0
        let _ = var_assign.add_shared_var_interval(Variable::new("x1"), interval_0.clone());

        let sym_var_assign = cs.get_sym_var_assignment(var_assign.clone());

        let removed = initial_states.remove_assignment(&sym_var_assign);
        assert!(removed.is_empty());

        let mut var_assign2 = VariableAssignment::new();
        // x0 in I_1
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
        let _ = var_assign2.add_shared_var_interval(Variable::new("x0"), interval_1.clone());
        // x1 in I_0
        let _ = var_assign2.add_shared_var_interval(Variable::new("x1"), interval_0.clone());

        let sym_var_assign2 = cs.get_sym_var_assignment(var_assign2.clone());

        let removed2 = initial_states.remove_assignment(&sym_var_assign2);
        assert!(removed2.equal(&initial_states));

        let changed_initial_states = initial_states.union(&ZCSStates {
            set_of_states: sym_var_assign2.assignment_bdd().clone(),
        });
        let removed3 = changed_initial_states.remove_assignment(&sym_var_assign2);
        assert!(removed3.equal(&initial_states));

        let removed4 = changed_initial_states.remove_assignment(&sym_var_assign);
        assert!(removed4.equal(&ZCSStates {
            set_of_states: sym_var_assign2.assignment_bdd().clone()
        }));
    }

    #[test]
    fn test_symbolic_transition() {
        let ata = get_ata();
        let builder: ZCSBuilder = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata);
        let cs = builder.build();

        let mut t_0: Option<&SymbolicTransition> = None;
        for t in &cs.transitions {
            if t.abstract_rule().id() == 0 {
                t_0 = Some(t);
            }
        }
        assert!(t_0.is_some());
        let t_0 = t_0.unwrap();

        let r_0 = t_0.abstract_rule();
        let r_0_bdd = t_0.transition_bdd.clone();

        let sym_trans = SymbolicTransition::new(r_0_bdd.clone(), r_0.clone());
        assert_eq!(sym_trans.abstract_rule, *r_0);
        assert!(sym_trans.transition_bdd.eq(&r_0_bdd));
    }
}

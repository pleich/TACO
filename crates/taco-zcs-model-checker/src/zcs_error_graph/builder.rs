//! Factory method to construct a symbolic error graph (ZCS error graph)
//! for a symbolic 01-CS (ZCS) and a set of error states.

use super::{ZCS, ZCSErrorGraph, ZCSStates};

/// Builder for constructing a symbolic error graph (ZCS error graph)
///
/// This builder takes a symnbolic 01-CS (ZCS) and a set of error states
/// and derives the corresponding symbolic error graph.
///
/// The builder performs backwards reachability of all states in the 01-CS starting
/// from the set of error states.
#[derive(Debug)]
pub struct ZCSErrorGraphBuilder<'a> {
    /// symbolic error graph that is constructed by the builder
    error_graph: ZCSErrorGraph<'a>,
}
impl<'a> ZCSErrorGraphBuilder<'a> {
    /// creates a new symbolic error graph builder
    pub fn new(cs: ZCS<'a>, err_states: ZCSStates) -> Self {
        ZCSErrorGraphBuilder {
            error_graph: ZCSErrorGraph {
                error_states: err_states,
                explored_states: Vec::new(),
                initial_states: cs.new_empty_sym_state(),
                cs,
            },
        }
    }

    /// predecessor computation to compute the reachable states
    ///
    /// # Pseudocode
    ///
    /// ```pseudo
    ///  unexplored ← error_states
    ///  visited ← unexplored
    ///  while (unexplored ≠ ∅) {
    ///     // 1. add new reachable states
    ///     explored_states.push(unexplored)
    ///     
    ///     // 2. update unexplored
    ///     unexplored ← Pred(∃ rule_vars: unexplored) ∧ ¬visited
    ///    
    ///     // 3. update visited
    ///     visited ← visited ∨ unexplored
    ///     abstract_unexplored ← ∃_rule_vars: unexplored
    ///   
    ///     for i in 0..|explored_states| {
    ///         // 4. for each level i, check if a state `s` has already been reached with a different rule
    ///         already_explored ← explored_states(i) ∧ abstract_unexplored
    ///
    ///         if (already_explored ≠ ∅) {
    ///             abstract_already_explored ← ∃ rule_vars: already_explored
    ///
    ///             // 5. add state `s` with new outgoing rule `r` to the set of already explored states
    ///             error_states(i) ← error_states(i) ∨ (unexplored ∧ abstract_already_explored)
    ///       
    ///             // 6. remove `s` from the set of unexplored states
    ///             abstract_unexplored ← abstract_unexplored ∧ ¬abstract_already_explored
    ///             unexplored ← unexplored ∧ ¬abstract_already_explored
    ///         }
    ///     }
    ///  }
    /// ```
    pub fn compute_explored_states(&mut self) {
        // unexplored states where the predecessor is computed from next
        let mut unexplored = self.error_graph.error_states.clone();
        // all states that are already visited
        // don't need to compute the predecessor for these states
        let mut visited = unexplored.clone();
        while !unexplored.is_empty() {
            // 1. add new reachable states
            self.error_graph.explored_states.push(unexplored.clone());
            // 2. update unexplored (compute predecessor and remove visited states)
            unexplored = self
                .error_graph
                .cs
                .compute_predecessor(self.error_graph.cs.abstract_rule_vars(unexplored.clone()));
            unexplored = unexplored.intersection(&visited.complement());
            // 3. update visited
            visited = visited.union(&unexplored);
            let mut abstract_unexplored =
                self.error_graph.cs.abstract_rule_vars(unexplored.clone());
            for i in 0..self.error_graph.explored_states.len() {
                // 4. for each level, check if a state `s` has already been reached with a different rule
                let already_explored =
                    self.error_graph.explored_states[i].intersection(&abstract_unexplored);
                if !already_explored.is_empty() {
                    let abstract_already_explored =
                        self.error_graph.cs.abstract_rule_vars(already_explored);
                    // 5. add state `s` with new outgoing rule `r` to the set of already explored states
                    self.error_graph.explored_states[i] = self.error_graph.explored_states[i]
                        .union(&unexplored.intersection(&abstract_already_explored));
                    // 6. remove `s` from the set of unexplored states
                    abstract_unexplored =
                        abstract_unexplored.intersection(&abstract_already_explored.complement());
                    unexplored = unexplored.intersection(&abstract_already_explored.complement());
                }
            }
        }
    }

    /// extracts all initial states that are reached in the error graph
    pub fn compute_reachable_initial_states(&mut self) {
        let mut initial_states = self.error_graph.cs.new_empty_sym_state();
        for symbolic_state in self.error_graph.explored_states.iter() {
            initial_states = initial_states
                .union(&(symbolic_state.intersection(&self.error_graph.cs.initial_states())))
        }
        self.error_graph.initial_states = initial_states
    }

    /// builds the symbolic error graph
    pub fn build(mut self) -> ZCSErrorGraph<'a> {
        self.compute_explored_states();
        self.compute_reachable_initial_states();
        self.error_graph
    }
}

#[cfg(test)]
mod tests {
    use taco_interval_ta::builder::IntervalTABuilder;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::Threshold;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::WeightedSum;

    use crate::ZCSErrorGraphBuilder;
    use crate::zcs;
    use taco_interval_ta::IntervalTAAction;
    use taco_interval_ta::IntervalTARule;
    use taco_interval_ta::interval::Interval;
    use taco_interval_ta::interval::IntervalBoundary;
    use taco_interval_ta::{IntervalActionEffect, IntervalConstraint};
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::ParameterConstraint;
    use taco_threshold_automaton::expressions::fraction::Fraction;

    use std::vec;
    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_threshold_automaton::expressions::{Location, Variable};
    use taco_threshold_automaton::{
        BooleanVarConstraint, LocationConstraint,
        expressions::{ComparisonOp, IntegerExpression, Parameter},
        general_threshold_automaton::{Action, builder::RuleBuilder},
    };
    use zcs::builder::ZCSBuilder;

    /// Used to construct the 01-CS for the following threshold automaton:
    ///
    /// # Example
    ///
    /// Threshold Automaton:
    ///     Locations: {l0,l1,l2}
    ///     Initial location: l0
    ///     Parameter: {n,t}
    ///     Shared Variable: x
    ///     Initial location constraints: l0 = n - t & l1 = 0 & l2
    ///     Rules:
    ///         r0: l0 -> l1, guard: true, action: x = x + 1
    ///         r1: l0 -> l2, guard: x >= n - t, action: none
    ///         r2: l1 -> l2, guard: x >= n - t, action: none
    ///
    /// Abstract Thershold Automaton:
    /// Intervals for x: I_0 = [0,1), I_1 = [1,n-t), I_2 = [n-t, infty)
    /// Interval Order: I_0 < I_1 < I_2
    /// Abstract Rules:
    ///     r0: l0 -> l1, guard: true, action: x = x + 1
    ///     r1: l0 -> l1, guard: x = I_2, action: none
    ///     r2: l1 -> l2, guard: x = I_2, action: none
    ///
    /// Structure of the symbolic 01-counter system:
    ///     [(1,0,0),I_0] --- r0 ---> [(-,1,0),{I_0,I_1}]
    ///     [(-,1,0),{I_0,I_1}] --- r0 ---> [(-,1,0),{I_0,I_1,I_2}]
    ///     [(-,1,0),{I_0,I_1,I_2}] --- r0 ---> [(-,1,0),{I_0,I_1,I_2}]
    ///     [(-,1,0),I_2] --- r1 ---> [(-,1,1),I_2]
    ///     [(-,1,0),I_2] --- r2 ---> [(-,-,1),I_2]
    ///
    /// The backwards reachability analysis for the set of error states {[(0,0,1),-]} looks as follows (already visited states are ignored):
    ///     level 1: [(0,0,1),-] <---- r1 ---- [(1,0,-),I_2],
    ///              [(0,0,1),-] <---- r2 ---- [(0,1,-),I_2]
    ///     level 2: [(1,0,-),I_2] <--- r2 --- [(1,1,-),I_2],
    ///              [(0,1,-),I_2] <--- r1 --- [(1,1,-),I_2],
    ///              [(0,1,-),I_1] <--- r0 --- [(1,-,-),{I_1,I_2}],
    ///     level 3: [(1,-,-),{I_1,I_2}] <--- r0 --- [(1,-,-),{I_0,I_1,I_2}]
    ///
    /// The symbol error graph for the set of error    lia_threshold_automaton::WeightedSum,states {[(0,0,1),-]} looks as follows:
    ///     level 0: {[(0,0,1),-]}
    ///     level 1: {[(1,0,-),I_2]&r1, [(0,1,-),I_2]&r2} \cup {[(1,0,-),I_2]&r0]} (added in level 3)
    ///     level 2: {[(1,-,-),I_1]&r0), [(1,1,-),I_2] &(r0 | r1 | r2)} (&r1,r2 added in the next iteration)
    ///     level 3: {[(1,-,-),I_0]&r0}
    fn get_test_ata() -> IntervalThresholdAutomaton {
        let ta_builder =
            taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder::new("test")
                .with_locations(vec![
                    Location::new("l0"),
                    Location::new("l1"),
                    Location::new("l2"),
                ])
                .unwrap()
                .with_variable(Variable::new("x"))
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
                        Box::new(IntegerExpression::Atom(Location::new("l0"))),
                        ComparisonOp::Eq,
                        Box::new(
                            IntegerExpression::Param(Parameter::new("n"))
                                - IntegerExpression::Param(Parameter::new("t")),
                        ),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("l2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap().with_resilience_conditions([ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Parameter::new("n")) - IntegerExpression::Atom(Parameter::new("t"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )]).unwrap().with_initial_variable_constraints([BooleanVarConstraint::ComparisonExpression(Box::new(IntegerExpression::Atom(Variable::new("x"))), ComparisonOp::Eq, Box::new(IntegerExpression::Const(0)))]).unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("l0"), Location::new("l1"))
                        .with_action(
                            Action::new(
                                Variable::new("x"),
                                IntegerExpression::Atom(Variable::new("x"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(1, Location::new("l0"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Geq,
                            Box::new(
                                IntegerExpression::Param(Parameter::new("n"))
                                    - IntegerExpression::Param(Parameter::new("t")),
                            ),
                        ))
                        .build(),
                    RuleBuilder::new(2, Location::new("l1"), Location::new("l2"))
                        .with_guard(BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
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
        let ata = interval_tas.next().unwrap();

        let nxt = interval_tas.next();
        assert!(nxt.is_none(), "Got additional ta {}", nxt.unwrap());

        ata
    }

    #[test]
    fn test_compute_reachable_initial_states() {
        let ata = get_test_ata();
        let cs = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata).build();

        let l0 = cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = cs.get_sym_state_for_loc(&Location::new("l2"));
        let error_states = l0
            .complement()
            .intersection(&l1.complement())
            .intersection(&l2);

        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));
        let abstract_rule_0 = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            vec![IntervalTAAction::new(
                Variable::new("x"),
                IntervalActionEffect::Inc(1),
            )],
        );
        let r0 = cs.get_sym_state_for_rule(&abstract_rule_0);
        let i0 = cs.get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0);
        let correct_initial_states = l0
            .intersection(&l1.complement())
            .intersection(&l2.complement())
            .intersection(&i0)
            .intersection(&r0);

        let builder = ZCSErrorGraphBuilder::new(cs, error_states);
        let error_graph = builder.build();
        let initial_states = error_graph.initial_states;

        assert!(correct_initial_states.equal(&initial_states));
    }

    #[test]
    fn test_compute_explored_states() {
        let ata = get_test_ata();
        let cs = ZCSBuilder::new(&taco_bdd::BDDManager::default(), &ata).build();
        let l0 = cs.get_sym_state_for_loc(&Location::new("l0"));
        let l1 = cs.get_sym_state_for_loc(&Location::new("l1"));
        let l2 = cs.get_sym_state_for_loc(&Location::new("l2"));
        let error_states = l0
            .complement()
            .intersection(&l1.complement())
            .intersection(&l2);

        // I_0 = [0,1)
        let interval_0 =
            Interval::new_constant(Fraction::new(0, 1, false), Fraction::new(1, 1, false));
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

        let i0 = cs.get_sym_state_for_shared_interval(&Variable::new("x"), &interval_0);
        let i1 = cs.get_sym_state_for_shared_interval(&Variable::new("x"), &interval_1);
        let i2 = cs.get_sym_state_for_shared_interval(&Variable::new("x"), &interval_2);

        // abstract rules
        // r0: l0 -> l1, guard: true, action: x = x + 1
        let abstract_rule_0 = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            vec![IntervalTAAction::new(
                Variable::new("x"),
                IntervalActionEffect::Inc(1),
            )],
        );
        // r1: l0 -> l2, guard: x = I_2, action: none
        let abstract_rule_1 = IntervalTARule::new(
            1,
            Location::new("l0"),
            Location::new("l2"),
            IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("x"),
                [interval_2.clone()].to_vec(),
            ),
            Vec::new(),
        );
        // r2: l1 -> l2, guard: x = I_2, action: none
        let abstract_rule_2 = IntervalTARule::new(
            2,
            Location::new("l1"),
            Location::new("l2"),
            IntervalConstraint::SingleVarIntervalConstr(
                Variable::new("x"),
                [interval_2.clone()].to_vec(),
            ),
            Vec::new(),
        );

        let r0 = cs.get_sym_state_for_rule(&abstract_rule_0);
        let r1 = cs.get_sym_state_for_rule(&abstract_rule_1);
        let r2 = cs.get_sym_state_for_rule(&abstract_rule_2);

        let builder = ZCSErrorGraphBuilder::new(cs.clone(), error_states.clone());

        let error_graph = builder.build();

        assert_eq!(error_graph.explored_states.len(), 4);

        // level 0: {[(0,0,1),-]} = error_states
        assert!(error_graph.explored_states[0].equal(&error_states));

        // level 1: {[(1,0,-),I_2]&(r0 | r1), [(0,1,-),I_2]&r2}
        let mut level1 = l0
            .intersection(&l1.complement())
            .intersection(&i2)
            .intersection(&(r0.union(&r1)));
        level1 = level1.union(
            &(l0.complement()
                .intersection(&l1)
                .intersection(&i2)
                .intersection(&r2)),
        );
        assert!(error_graph.explored_states[1].equal(&level1));

        // level 2: {[(1,-,-),I_1]&r0), [(1,1,-),I_2] &(r0 | r1 | r2)}
        let mut level2 = l0.intersection(&i1).intersection(&r0);
        level2 = level2.union(
            &(l0.intersection(&l1)
                .intersection(&i2)
                .intersection(&(r0.union(&r1).union(&r2)))),
        );
        // this constraint needs to be added due to the construction of the symbolic transition
        // because the guard for r0 is true even though "I_3" does not exist: [(1,-,-), !(I_0 | I_1 | I_2)] &r0
        level2 = level2.union(
            &(l0.intersection(&(i0.union(&i1).union(&i2)).complement())
                .intersection(&r0)),
        );
        assert!(error_graph.explored_states[2].equal(&level2));

        // level 3: {[(1,-,-),I_0]&r0}
        let level3 = l0.intersection(&i0).intersection(&r0);
        assert!(error_graph.explored_states[3].equal(&level3));
    }
}

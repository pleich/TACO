//! Module for encoding possible paths between configurations in a threshold
//! automaton
//!
//! This module implements an encoding of potential paths in an (extended)
//! threshold automaton. The encoding is described in the paper
//! ["Complexity of Verification and Synthesis of Threshold Automata"](https://arxiv.org/abs/2002.08507)
//! by A. R. Balasubramanian, Javier Esparza, Marijana Lazic.
//!
//! The paper does not provide a complete encoding of the threshold automata,
//! instead many implementation details are not provided. As we were not
//! provided with the source code (nor an executable) of the implementation used
//! in the paper, we  had to make some assumptions about the implementation
//! details.
//!
//! We will explicitly mark functions that are not directly described in the
//! paper.

use std::{
    collections::{BTreeMap, HashMap},
    fmt,
    rc::Rc,
};

use taco_threshold_automaton::{
    ActionDefinition, RuleDefinition, ThresholdAutomaton, VariableConstraint,
    expressions::{Location, Parameter, Variable},
    general_threshold_automaton::{Rule, UpdateExpression},
};

use crate::{
    SMTExpr, SMTSolution, SMTSolver,
    expression_encoding::{DeclaresVariable, EncodeToSMT, SMTSolverError, SMTVariableContext},
};

/// Trait implemented by symbolic steps
pub trait StepSMT: SMTVariableContext<Rule> {
    /// Returns the number of times a rule has been applied in the solution to
    /// this context
    fn get_rules_applied(
        &self,
        solver: &mut SMTSolver,
        res: SMTSolution,
    ) -> Result<impl Iterator<Item = (Rule, u32)>, SMTSolverError> {
        let rules_used = self.get_solution(solver, res)?;

        Ok(rules_used.into_iter().filter(|(_, n)| *n > 0))
    }
}

/// Context for rule applications in a path on a threshold automaton
///
/// This context creates SMT variables for rule applications for all rules that
/// were supplied during the context creation.
///
/// It then allows to encode the possible paths using the
/// [`LazyStepContext::encode_phi_step`] and
/// [`LazyStepContext::encode_phi_steady`] functions.
#[derive(Debug, Clone)]
pub struct LazyStepContext<TA, C>
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>,
{
    /// index of the configuration
    index: usize,
    /// variables for rules
    rule_vars: BTreeMap<Rule, SMTExpr>,
    /// threshold automaton
    ta: Rc<TA>,
    /// previous configuration
    prev_config: Rc<C>,
    /// current configuration
    curr_config: Rc<C>,
}

impl<TA, C> SMTVariableContext<Rule> for LazyStepContext<TA, C>
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>,
{
    fn get_expr_for(&self, expr: &Rule) -> Result<SMTExpr, SMTSolverError> {
        self.rule_vars
            .get(expr)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredRule(expr.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Rule>
    where
        Rule: 'a,
    {
        self.rule_vars.keys()
    }

    fn get_solution<'a>(
        &'a self,
        solver: &mut crate::SMTSolver,
        res: crate::SMTSolution,
    ) -> Result<HashMap<Rule, u32>, super::SMTSolverError>
    where
        Rule: 'a + Eq + std::hash::Hash + Clone,
    {
        match res {
            crate::SMTSolution::UNSAT => Err(super::SMTSolverError::ExtractionFromUnsat),
            crate::SMTSolution::SAT => {
                let expr_vec = self
                    .get_exprs()
                    .into_iter()
                    .map(|t| self.get_expr_for(t))
                    .collect::<Result<Vec<_>, _>>()?;

                let solution = solver.get_value(expr_vec)?;

                solution
                    .into_iter()
                    .zip(self.get_exprs())
                    .map(|((_, sol), t)| {
                        let solution_value = solver.get_u32(sol).ok_or_else(|| {
                            let sol = solver.display(sol);
                            super::SMTSolverError::SolutionExtractionParseIntError(sol.to_string())
                        })?;

                        Ok((t.clone(), solution_value))
                    })
                    .collect::<Result<HashMap<Rule, u32>, super::SMTSolverError>>()
            }
        }
    }
}

impl<TA, C> LazyStepContext<TA, C>
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>,
{
    /// Create a new step context for encoding a step between two configurations
    /// σ and σ'
    ///
    /// A step context stores the rule variables that are needed to specify the
    /// transition between two configurations of a threshold automaton.
    pub fn new(
        rules_to_appl: impl Iterator<Item = Rule>,
        ta: Rc<TA>,
        prev_config: Rc<C>,
        curr_config: Rc<C>,
        index: usize,
        solver: &mut SMTSolver,
    ) -> LazyStepContext<TA, C> {
        let rule_vars = rules_to_appl
            .into_iter()
            .map(|r| {
                let rule = r
                    .declare_variable(solver, index as u32)
                    .expect("Failed to declare rule variable");
                solver
                    .assert(solver.gte(rule, solver.numeral(0)))
                    .expect("Failed to assert rule application >= 0");

                (r.clone(), rule)
            })
            .collect();

        Self {
            index,
            ta,
            rule_vars,
            prev_config,
            curr_config,
        }
    }

    /// Encodes the ϕ_{base} of the step context
    ///
    /// The encoding of phi base is slightly modified to require less
    /// parameters, the encoding does not include:
    /// - the constraint σ.p = σ'.p for all parameters p
    /// - the constraint RC(σ.p)
    /// - the constraint N(σ.p) = N(σ'.p)
    ///
    /// This is because we assume that the valuation of the parameters does not
    /// change during the execution. Therefore we instead only need to encode
    /// the resilience conditions once, which is done in the context manager.
    /// Afterwards, we can simply use the global parameter variables.
    fn encode_phi_base(&self, solver: &SMTSolver) -> SMTExpr {
        if self.rule_vars.is_empty() {
            return solver.true_();
        }

        // ω(σ) = ω(σ')
        solver.and_many(
            self.rule_vars
                .keys()
                .map(|rule| rule.guard().as_boolean_expr())
                .map(|guard| {
                    let prev_sat_guard = guard
                        .encode_to_smt_with_ctx(solver, self.prev_config.as_ref())
                        .expect("Failed to encode guard with previous configuration");
                    let curr_sat_guard = guard
                        .encode_to_smt_with_ctx(solver, self.curr_config.as_ref())
                        .expect("Failed to encode guard with current configuration");

                    solver.eq(prev_sat_guard, curr_sat_guard)
                }),
        )
    }

    /// Encodes the ϕ_L of the step context
    fn encode_phi_l(&self, solver: &SMTSolver) -> SMTExpr {
        if self.ta.locations().count() == 0 {
            return solver.true_();
        }

        solver.and_many(self.ta.locations().map(|loc| {
            // σ.κ(ℓ)
            let prev_loc = self
                .prev_config
                .get_expr_for(loc)
                .expect("Failed to get location for ϕ_L");
            // σ′.κ(ℓ)
            let curr_loc = self
                .curr_config
                .get_expr_for(loc)
                .expect("Failed to get location for ϕ_L");

            // σ′.κ(ℓ) - σ.κ(ℓ)
            let diff_loc_state = solver.sub(curr_loc, prev_loc);

            // ∑_{i=1}^{a_l} x_{in_i^l}
            let in_sum = solver.plus_many(
                self.rule_vars
                    .iter()
                    .filter(|(r, _)| r.target() == loc) // incoming rules
                    .map(|(_, x_r)| *x_r)
                    .chain([solver.numeral(0)]), // required to prevent panic if there are no incoming rules
            );

            // ∑_{j=1}^{b_l} x_{out_j^l}
            let out_sum = solver.plus_many(
                self.rule_vars
                    .iter()
                    .filter(|(r, _)| r.source() == loc) // outgoing rules
                    .map(|(_, x_r)| *x_r)
                    .chain([solver.numeral(0)]), // required to prevent panic if there are no outgoing rules
            );

            // ∑_{i=1}^{a_l} x_{in_i^l} - ∑_{j=1}^{b_l} x_{out_j^l}
            let diff_rule_appl = solver.sub(in_sum, out_sum);

            solver.eq(diff_loc_state, diff_rule_appl)
        }))
    }

    /// Encodes the ϕ_Γ of the step context
    fn encode_phi_gamma(&self, solver: &SMTSolver) -> SMTExpr {
        if self.ta.variables().count() == 0 {
            return solver.true_();
        }

        // z ∈ Γ
        solver.and_many(self.ta.variables().map(|z| {
            // σ.g[z]
            let prev_var = self
                .prev_config
                .get_expr_for(z)
                .expect("Failed to get variable for ϕ_Γ");
            // σ'.g[z]
            let curr_var = self
                .curr_config
                .get_expr_for(z)
                .expect("Failed to get variable for ϕ_Γ");

            // σ'.g[z] - σ.g[z]
            let diff_var_state = solver.sub(curr_var, prev_var);

            // ∑_{r ∈ R} x_r * r.u[z]
            let update_acc = solver.plus_many(
                self.rule_vars
                    .iter()
                    .map(|(r, x_r)| {
                        let mut acts = r.actions().filter(|a| a.variable() == z && !a.is_reset());

                        let act = acts.next();
                        if act.is_none() {
                            return solver.numeral(0);
                        }

                        debug_assert!(
                            acts.next().is_none(),
                            "Multiple actions on same variable should have been rejected !"
                        );

                        let act = act.unwrap();

                        debug_assert!(
                            !act.is_reset(),
                            "This model checker does not support resets !"
                        );

                        // r.u[z]
                        let update = Self::update_vec_to_smt(act.update(), solver);

                        // x_r * r.u[z]
                        solver.times(*x_r, update)
                    })
                    .chain([solver.numeral(0)]), // prevent panics in case there are 0 rules
            );

            // (∑_{r ∈ R} x_r * r.u[z]) = σ'.g[z] - σ.g[z]
            let mut update = solver.eq(diff_var_state, update_acc);

            // Modification to the original encoding to support resets:
            // For any rule x_R resetting z:  x_R > 0 && σ'.g[z] = 0
            let reset_effect = self
                .rule_vars
                .iter()
                .filter(|(r, _)| r.actions().any(|a| a.variable() == z && a.is_reset()))
                .map(|(_, x_r)| {
                    let x_r_gt_0 = solver.gt(*x_r, solver.numeral(0));
                    let curr_var_eq_0 = solver.eq(curr_var, solver.numeral(0));

                    solver.and(x_r_gt_0, curr_var_eq_0)
                })
                .collect::<Vec<_>>();

            // either the variable supports the update, or the variable has been reset
            if !reset_effect.is_empty() {
                // Sum over all reseting rules = 0 => no reset applied
                let no_reset_applied = solver.eq(
                    solver.plus_many(
                        self.rule_vars
                            .iter()
                            .filter(|(r, _)| r.actions().any(|a| a.variable() == z && a.is_reset()))
                            .map(|(_, x_r)| *x_r),
                    ),
                    solver.numeral(0),
                );

                update = solver.or(
                    solver.and(update, no_reset_applied), // if there is no reset: update must hold
                    solver.or_many(reset_effect),         // if a reset is applied, = 0
                );
            }

            update
        }))
    }

    /// Encodes the ϕ_R of the step context
    fn encode_phi_r(&self, solver: &SMTSolver) -> SMTExpr {
        if self.rule_vars.is_empty() {
            return solver.true_();
        }

        solver.and_many(self.rule_vars.iter().map(|(rule, x_r)| {
            // x_r > 0
            let rule_applied = solver.gt(*x_r, solver.numeral(0));

            // σ ⊧ r.ϕ
            let guard_sat = rule
                .guard()
                .encode_to_smt_with_ctx(solver, self.prev_config.as_ref())
                .expect("Failed to encode guard with previous configuration");

            // x_r > 0 => (σ ⊧ r.ϕ)
            solver.imp(rule_applied, guard_sat)
        }))
    }

    /// (Exponential) Encode ϕ_{appl}
    ///
    /// This function encodes an exponential version of the formula ϕ_{appl},
    /// which includes all possibilities to fire a rule.
    ///
    /// Compared to the version described in the main section of the paper, we
    /// statically filter the set S, to only include chains where for all i it
    /// holds that
    ///     r_i.to = r_{i+1}.from and r_s = r
    /// therefore reducing the size of the set S and eliminating the need to
    /// encode
    ///     ∧_{1 < i ≤ s} r_{i-1}.to = r_i.from ∧ r_s = r
    /// into the formula.
    ///
    /// Note that we can therefore still have an exponentially big formula. To
    /// avoid this, non-deterministic guessing would need to be implemented.
    fn exponential_encode_phi_appl(&self, solver: &SMTSolver) -> SMTExpr {
        if self.rule_vars.is_empty() {
            return solver.true_();
        }

        solver.and_many(self.rule_vars.iter().map(|(rule, x_r)| {
            // x_r > 0
            let xr_gt_0 = solver.gt(*x_r, solver.numeral(0));

            // S ∈ 2^R
            let all_possible_s = self.compute_s_for_r(rule);

            // prevent panics if there is no applicable chain
            if all_possible_s.is_empty() {
                return solver.false_();
            }

            // ∨_S ∈ 2^R ф_{chain}
            let disj_s = solver.or_many(
                all_possible_s
                    .iter()
                    .map(|s| self.encode_phi_chain(solver, s)),
            );

            //  x_r > 0 => ∨_S ∈ 2^R ф_{chain}
            let mut res = solver.imp(xr_gt_0, disj_s);

            // Modification to the original encoding to support resets:
            // if a reset rule is applied during a steady step, we must already
            // be in a zero interval
            if rule.actions().any(|a| a.is_reset()) {
                let reset_var_already_zero =
                    solver.and_many(rule.actions().filter(|a| a.is_reset()).map(|a| {
                        let v = self.prev_config.get_expr_for(a.variable()).unwrap();
                        solver.eq(v, solver.numeral(0))
                    }));
                let reset_applied_imp_0 = solver.imp(xr_gt_0, reset_var_already_zero);

                res = solver.and(res, reset_applied_imp_0)
            }

            // Modification to support decrements:
            // In a steady step either only increments or only decrements can be
            // applied
            if self
                .rule_vars
                .iter()
                .any(|(r, _)| r.actions().any(|a| a.is_decrement()))
                && self
                    .rule_vars
                    .iter()
                    .any(|(r, _)| r.actions().any(|a| a.is_increment()))
            {
                // sum over all rules with decrements
                let r_dec = solver.plus_many(
                    self.rule_vars
                        .iter()
                        .filter(|(r, _)| r.actions().any(|a| a.is_decrement()))
                        .map(|(_, x_r)| *x_r),
                );
                // sum over all rules with increments
                let r_inc = solver.plus_many(
                    self.rule_vars
                        .iter()
                        .filter(|(r, _)| r.actions().any(|a| a.is_increment()))
                        .map(|(_, x_r)| *x_r),
                );

                // an increment rule is applied
                let r_inc_gt_0 = solver.gt(r_inc, solver.numeral(0));
                // a decrement rule is applied
                let r_dec_gt_0 = solver.gt(r_dec, solver.numeral(0));

                // only increments or decrements
                let dec_xor_inc = solver.and(
                    solver.imp(r_inc_gt_0, solver.not(r_dec_gt_0)),
                    solver.imp(r_dec_gt_0, solver.not(r_inc_gt_0)),
                );

                res = solver.and(res, dec_xor_inc);
            }

            res
        }))
    }

    /// Encode ϕ_chain for a single non-deterministic guess
    ///
    /// This function encodes the ϕ_{chain} for set of rules s
    /// However, this function only encodes ∧_{r ∈ s} x_r > 0 ∧ σ.k(r_1.from) > 0
    /// as all other constraints can be statically checked during the
    /// computation of S
    ///
    /// Note: This function expects the sequence of rules to be reversed !
    fn encode_phi_chain(&self, solver: &SMTSolver, s: &[&Rule]) -> SMTExpr {
        if s.is_empty() {
            return solver.true_();
        }

        // σ.k(r_1.from) > 0
        let loc = s.last().unwrap().source(); // change if not reversed
        let loc_var = self
            .prev_config
            .get_expr_for(loc)
            .expect("Failed to get location for ϕ_chain");
        let loc_gt_0 = solver.gt(loc_var, solver.numeral(0));

        solver.and_many(
            s.iter()
                .map(|rule| {
                    let x_r = self.get_expr_for(rule).expect("Rule variable not found");

                    solver.gt(x_r, solver.numeral(0))
                })
                .chain([loc_gt_0]),
        )
    }

    /// Compute all sets possible values of S for rule r
    ///
    /// This function computes all possible sets S for all rules r, where S is
    /// the set of rules that can lead up to r.
    /// Additionally, this function ensures that these sets are chainable,
    /// meaning they satisfy the formula:
    ///     ∧_{1< i ≤ s} r_{i-1}.to = r_i.from ∧ r_s = r
    ///
    /// This function uses the helper `compute_s_with_backtracking_recursive`,
    /// to directly compute only chainable rule sequences.
    ///
    /// Note: **This function returns the sequences to apply in reversed
    /// order!**. You can use `.rev()` to iterate in reversed order.
    fn compute_s_for_r<'a>(&'a self, r: &'a Rule) -> Vec<Vec<&'a Rule>> {
        let loc = r.source();
        self.compute_s_with_backtracking_recursive(loc, vec![r])
    }

    /// Recursive helper function that returns a vector that
    /// contains:
    ///  - the current sequence of chainable rules
    ///  - the current sequence of rules extended with the incoming rules into
    ///    `loc`
    ///  - the chainable extensions for these rule sequences
    ///
    /// Note: Chains will be returned in reverse order !
    fn compute_s_with_backtracking_recursive<'a>(
        &'a self,
        loc: &'a Location,
        rules_applied: Vec<&'a Rule>,
    ) -> Vec<Vec<&'a Rule>> {
        // get incoming rules into loc, these will be chainable
        let mut s = self
            .rule_vars
            .iter()
            .filter(|(r, _)| r.target() == loc) //incoming rules
            .filter(|(r, _)| !rules_applied.contains(r))
            .flat_map(|(r, _)| {
                let loc = r.source();
                let mut rules_applied: Vec<_> = rules_applied.clone();
                rules_applied.push(r);

                self.compute_s_with_backtracking_recursive(loc, rules_applied)
            })
            .collect::<Vec<_>>();

        // current sequence is chainable, so add it
        s.push(rules_applied);

        s
    }

    /// Encode ϕ_{steady}
    pub fn encode_phi_steady(&self, solver: &SMTSolver) -> SMTExpr {
        let phi_base = self.encode_phi_base(solver);
        let phi_l = self.encode_phi_l(solver);
        let phi_gamma = self.encode_phi_gamma(solver);
        let phi_r = self.encode_phi_r(solver);
        let phi_appl = self.exponential_encode_phi_appl(solver);

        solver.and_many([phi_base, phi_l, phi_gamma, phi_r, phi_appl])
    }

    /// Encode reduced version of ϕ_{appl}
    ///
    /// That only requires that σ.k(r.source) > 0 for every self-loop if x_r > 0
    /// For other rules, correctness is ensured by the encoding of ϕ_Γ
    fn encode_appl_for_step_step(&self, solver: &SMTSolver) -> SMTExpr {
        if self
            .rule_vars
            .iter()
            .filter(|(r, _)| r.source() == r.target())
            .count()
            == 0
        {
            return solver.true_();
        }

        solver.and_many(
            self.rule_vars
                .iter()
                .filter(|(r, _)| r.source() == r.target())
                .map(|(rule, x_r)| {
                    // x_r > 0
                    let xr_gt_0 = solver.gt(*x_r, solver.numeral(0));

                    let src_loc_procs = self
                        .prev_config
                        .get_expr_for(rule.source())
                        .expect("Failed to get SMT variable for source location");

                    // σ.k(r.source) > 0
                    let src_loc_has_procs = solver.gt(src_loc_procs, solver.numeral(0));

                    // x_r > 0 => σ.k(r.source) > 0
                    solver.imp(xr_gt_0, src_loc_has_procs)
                }),
        )
    }

    /// Encode ϕ_{step}
    ///
    /// Encodes the ϕ_{step} of the step context
    ///
    /// # Implementation
    ///
    /// The paper does not (fully) specify the encoding of ϕ_{step}.
    ///
    /// We decided to use the following formula:
    ///  - Introduce a new set of rule variables x_r' for each rule r.
    ///  - Since we only want one rule to be applied when executing a step, we
    ///    require that the sum of the rule variables is equal to 1, i.e.:
    ///    ∑_{r ∈ R} x_r' ≤ 1
    ///  - Then we can encode the validity of the rule application by simply
    ///    using ϕ_R, ϕ_Γ and ϕ_L, with the new variables
    ///  - **Important**: Instead of using ϕ_{appl} with ϕ_{chain}, we use the
    ///    encoding provided by `encode_appl_for_step_step`, which is
    ///    specifically designed for step contexts and ensures the correct
    ///    application of rules in this setting.
    ///
    pub fn encode_phi_step(&self, solver: &SMTSolver) -> SMTExpr {
        let phi_l = self.encode_phi_l(solver);
        let phi_gamma = self.encode_phi_gamma(solver);
        let phi_r = self.encode_phi_r(solver);
        let phi_appl = self.encode_appl_for_step_step(solver);

        // ∑_{r ∈ R} x_r' ≤ 1
        let at_most_one_rule_applied = solver.lte(
            solver.plus_many(self.rule_vars.values().cloned().chain([solver.numeral(0)])),
            solver.numeral(1),
        );

        solver.and_many([phi_l, phi_gamma, phi_r, at_most_one_rule_applied, phi_appl])
    }

    /// Encode the effect of an UpdateExpression into an SMT expression
    ///
    /// This function encodes the effect of the update `upd` to a variable
    /// into an SMT expression.
    fn update_vec_to_smt(upd: &UpdateExpression, solver: &SMTSolver) -> SMTExpr {
        match upd {
            UpdateExpression::Inc(i) => solver.numeral(*i),
            UpdateExpression::Dec(d) => {
                let dec = solver.numeral(*d);
                solver.negate(dec)
            }
            UpdateExpression::Reset => unreachable!("Resets should be handled before"),
            UpdateExpression::Unchanged => solver.numeral(0),
        }
    }
}

impl<TA, C> StepSMT for LazyStepContext<TA, C>
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>,
{
}

impl<TA, C> fmt::Display for LazyStepContext<TA, C>
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StepContext: {}", self.index)
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, rc::Rc};

    use taco_threshold_automaton::{
        ThresholdAutomaton,
        expressions::{
            BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Location,
            Variable,
        },
        general_threshold_automaton::{
            Action, UpdateExpression,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
    };

    use crate::{
        SMTSolverBuilder, SMTSolverContext,
        expression_encoding::{
            SMTVariableContext,
            config_ctx::ConfigCtx,
            step_ctx::{LazyStepContext, StepSMT},
        },
    };

    #[test]
    fn test_encode_phi_base() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ))
            .build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_guard(BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::False),
                BooleanConnective::Or,
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::True),
                    BooleanConnective::And,
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::Const(5)),
                    )),
                )),
            ))
            .build();

        // rule without any action
        let r3 = RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_base(&solver);

        let expected_smt = solver.and_many([
            // r1
            solver.imp(
                solver.gt(
                    config_0.get_expr_for(&Variable::new("var1")).unwrap(),
                    solver.numeral(1),
                ),
                solver.gt(
                    config_1.get_expr_for(&Variable::new("var1")).unwrap(),
                    solver.numeral(1),
                ),
            ),
            // r1
            solver.imp(
                solver.gt(
                    config_1.get_expr_for(&Variable::new("var1")).unwrap(),
                    solver.numeral(1),
                ),
                solver.gt(
                    config_0.get_expr_for(&Variable::new("var1")).unwrap(),
                    solver.numeral(1),
                ),
            ),
            // r2
            solver.imp(
                solver.lte(
                    config_0.get_expr_for(&Variable::new("var2")).unwrap(),
                    solver.numeral(5),
                ),
                solver.lte(
                    config_1.get_expr_for(&Variable::new("var2")).unwrap(),
                    solver.numeral(5),
                ),
            ),
            // r2
            solver.imp(
                solver.lte(
                    config_1.get_expr_for(&Variable::new("var2")).unwrap(),
                    solver.numeral(5),
                ),
                solver.lte(
                    config_0.get_expr_for(&Variable::new("var2")).unwrap(),
                    solver.numeral(5),
                ),
            ),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_base_no_panics() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_base(&solver);

        let expected_smt = solver.true_();

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_l() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_l(&solver);

        let expected_smt = solver.and_many([
            // loc1
            solver.eq(
                solver.sub(
                    config_1.get_expr_for(&Location::new("loc1")).unwrap(),
                    config_0.get_expr_for(&Location::new("loc1")).unwrap(),
                ),
                solver.sub(solver.numeral(0), step_context.get_expr_for(&r1).unwrap()),
            ),
            //loc2
            solver.eq(
                solver.sub(
                    config_1.get_expr_for(&Location::new("loc2")).unwrap(),
                    config_0.get_expr_for(&Location::new("loc2")).unwrap(),
                ),
                solver.sub(
                    step_context.get_expr_for(&r1).unwrap(),
                    step_context.get_expr_for(&r2).unwrap(),
                ),
            ),
            //loc3
            solver.eq(
                solver.sub(
                    config_1.get_expr_for(&Location::new("loc3")).unwrap(),
                    config_0.get_expr_for(&Location::new("loc3")).unwrap(),
                ),
                solver.sub(step_context.get_expr_for(&r2).unwrap(), solver.numeral(0)),
            ),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_phi_l_no_locations_does_not_panic() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .initialize()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );
        let got_smt_expr = step_context.encode_phi_l(&solver);

        let expected_smt = solver.true_();

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_gamma() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_actions([Action::new_with_update(
                Variable::new("var1"),
                UpdateExpression::Inc(1),
            )])
            .build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_actions([
                Action::new_with_update(Variable::new("var1"), UpdateExpression::Dec(1)),
                Action::new_with_update(Variable::new("var2"), UpdateExpression::Inc(3)),
                Action::new_with_update(Variable::new("var3"), UpdateExpression::Unchanged),
            ])
            .build();

        // rule without any action
        let r3 = RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_gamma(&solver);

        let expected_smt = solver.and_many([
            //var1
            solver.eq(
                solver.plus_many([
                    // update r1
                    step_context.get_expr_for(&r1).unwrap(),
                    // update r2
                    solver.times(
                        solver.negate(solver.numeral(1)),
                        step_context.get_expr_for(&r2).unwrap(),
                    ),
                ]),
                solver.sub(
                    config_1.get_expr_for(&Variable::new("var1")).unwrap(),
                    config_0.get_expr_for(&Variable::new("var1")).unwrap(),
                ),
            ),
            //var2
            solver.eq(
                solver.plus_many([
                    // update r2
                    solver.times(solver.numeral(3), step_context.get_expr_for(&r2).unwrap()),
                ]),
                solver.sub(
                    config_1.get_expr_for(&Variable::new("var2")).unwrap(),
                    config_0.get_expr_for(&Variable::new("var2")).unwrap(),
                ),
            ),
            //var3
            solver.eq(
                solver.numeral(0),
                solver.sub(
                    config_1.get_expr_for(&Variable::new("var3")).unwrap(),
                    config_0.get_expr_for(&Variable::new("var3")).unwrap(),
                ),
            ),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_gamma_no_variables_does_not_panic() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .initialize()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_gamma(&solver);

        let expected_smt = solver.true_();

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_r() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ))
            .build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_guard(BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::False),
                BooleanConnective::Or,
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::True),
                    BooleanConnective::And,
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::Const(5)),
                    )),
                )),
            ))
            .build();

        // rule without any action
        let r3 = RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_r(&solver);

        let expected_smt = solver.and_many([
            // r1
            solver.imp(
                solver.gte(step_context.get_expr_for(&r1).unwrap(), solver.numeral(1)),
                solver.gt(
                    config_0.get_expr_for(&Variable::new("var1")).unwrap(),
                    solver.numeral(1),
                ),
            ),
            // r2
            solver.imp(
                solver.gt(step_context.get_expr_for(&r2).unwrap(), solver.numeral(0)),
                solver.lte(
                    config_0.get_expr_for(&Variable::new("var2")).unwrap(),
                    solver.numeral(5),
                ),
            ),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_r_does_not_panic() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .initialize()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_gamma(&solver);

        let expected_smt = solver.true_();

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_encode_phi_appl() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.exponential_encode_phi_appl(&solver);

        let r1 = step_context.get_expr_for(&r1).unwrap();
        let r2 = step_context.get_expr_for(&r2).unwrap();

        let expected_smt = solver.and_many([
            // r1
            solver.imp(
                solver.gt(r1, solver.numeral(0)),
                solver.gt(
                    config_0.get_expr_for(&Location::new("loc1")).unwrap(),
                    solver.numeral(0),
                ),
            ),
            // r2
            solver.imp(
                solver.gt(r2, solver.numeral(0)),
                solver.or_many([
                    solver.gt(
                        config_0.get_expr_for(&Location::new("loc2")).unwrap(),
                        solver.numeral(0),
                    ),
                    solver.and_many([
                        solver.gt(r1, solver.numeral(0)),
                        solver.gt(
                            config_0.get_expr_for(&Location::new("loc1")).unwrap(),
                            solver.numeral(0),
                        ),
                    ]),
                ]),
            ),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_compute_s() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3")).build();
        let r3 = RuleBuilder::new(2, Location::new("loc3"), Location::new("loc4")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
                Location::new("loc4"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let s = step_context.compute_s_for_r(&r3);
        assert_eq!(s.len(), 3, "{s:?}");
        assert!(s.contains(&vec![&r3]), "{s:?}");
        assert!(s.contains(&vec![&r3, &r2,]), "{s:?}");
        assert!(s.contains(&vec![&r3, &r2, &r1]), "{s:?}");
    }

    #[test]
    fn test_encode_phi_step() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ))
            .build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variables([Variable::new("var1"), Variable::new("var2")])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_step(&solver);

        // tested before
        let phi_l = step_context.encode_phi_l(&solver);
        let phi_gamma = step_context.encode_phi_gamma(&solver);
        let phi_r = step_context.encode_phi_r(&solver);

        let r1 = step_context.get_expr_for(&r1).unwrap();
        let r2 = step_context.get_expr_for(&r2).unwrap();

        let expected_smt = solver.and_many([
            phi_l,
            phi_gamma,
            phi_r,
            // at most one rule applied
            solver.lte(solver.plus(r1, r2), solver.numeral(1)),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    #[test]
    fn test_get_rules_applied() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ))
            .build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_guard(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(42)),
            ))
            .build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variables([Variable::new("var1"), Variable::new("var2")])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let smt_expr = solver.and_many([
            solver.eq(step_context.get_expr_for(&r1).unwrap(), solver.numeral(4)),
            solver.eq(step_context.get_expr_for(&r2).unwrap(), solver.numeral(42)),
        ]);

        let res = solver.assert_and_check_expr(smt_expr).unwrap();
        let rules = step_context
            .get_rules_applied(&mut solver, res)
            .unwrap()
            .collect::<Vec<_>>();

        assert!(rules.contains(&(r1.clone(), 4)));
        assert!(rules.contains(&(r2.clone(), 42)));
    }

    #[test]
    fn test_encode_phi_gamma_with_reset() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let r1 = RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
            .with_actions([Action::new_with_update(
                Variable::new("var1"),
                UpdateExpression::Inc(1),
            )])
            .build();
        let r2 = RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
            .with_actions([
                Action::new_with_update(Variable::new("var1"), UpdateExpression::Dec(1)),
                Action::new_with_update(Variable::new("var2"), UpdateExpression::Inc(3)),
                Action::new_with_update(Variable::new("var3"), UpdateExpression::Reset),
            ])
            .build();

        // rule without any action
        let r3 = RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3")).build();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .with_rules([r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .build();

        let config_0 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            0,
        ));
        let config_1 = Rc::new(ConfigCtx::new(
            &mut solver,
            &test_ta,
            Rc::new(HashMap::new()),
            1,
        ));

        let step_context = LazyStepContext::new(
            test_ta.rules().cloned(),
            Rc::new(test_ta.clone()),
            config_0.clone(),
            config_1.clone(),
            0,
            &mut solver,
        );

        let got_smt_expr = step_context.encode_phi_gamma(&solver);

        let expected_smt = solver.and_many([
            //var1
            solver.eq(
                solver.plus_many([
                    // update r1
                    step_context.get_expr_for(&r1).unwrap(),
                    // update r2
                    solver.times(
                        solver.negate(solver.numeral(1)),
                        step_context.get_expr_for(&r2).unwrap(),
                    ),
                ]),
                solver.sub(
                    config_1.get_expr_for(&Variable::new("var1")).unwrap(),
                    config_0.get_expr_for(&Variable::new("var1")).unwrap(),
                ),
            ),
            //var2
            solver.eq(
                solver.plus_many([
                    // update r2
                    solver.times(solver.numeral(3), step_context.get_expr_for(&r2).unwrap()),
                ]),
                solver.sub(
                    config_1.get_expr_for(&Variable::new("var2")).unwrap(),
                    config_0.get_expr_for(&Variable::new("var2")).unwrap(),
                ),
            ),
            //var3
            solver.or(
                solver.and(
                    solver.eq(step_context.get_expr_for(&r2).unwrap(), solver.numeral(0)),
                    solver.eq(
                        solver.numeral(0),
                        solver.sub(
                            config_1.get_expr_for(&Variable::new("var3")).unwrap(),
                            config_0.get_expr_for(&Variable::new("var3")).unwrap(),
                        ),
                    ),
                ),
                solver.and(
                    solver.gt(step_context.get_expr_for(&r2).unwrap(), solver.numeral(0)),
                    solver.eq(
                        config_1.get_expr_for(&Variable::new("var3")).unwrap(),
                        solver.numeral(0),
                    ),
                ),
            ),
        ]);

        // the order of expressions might change so instead we check whether
        // there exists an assignment such that they are not equivalent
        let check_equivalent = solver.not(solver.and(
            solver.imp(got_smt_expr, expected_smt),
            solver.imp(expected_smt, got_smt_expr),
        ));

        assert!(
            !solver
                .assert_and_check_expr(check_equivalent)
                .unwrap()
                .is_sat(),
            "got     : {}\nexpected: {}",
            solver.display(got_smt_expr),
            solver.display(expected_smt)
        );
    }

    // TODO: tests for resets and decrements
}

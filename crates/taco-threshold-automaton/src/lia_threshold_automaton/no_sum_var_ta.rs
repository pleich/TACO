//! TODO: Replace this logic by implementing a smarter interval logic
//!
//! This module replaces all sums of variables by a new single variable, which
//! is always incremented / decremented when any of its components is
//! incremented or decremented.
//! This replacement is sound and complete, however it is expensive, as it might
//! generate more spurious paths.
//!
//! Instead this logic should be replaced by a better ordering that can validate
//! which intervals are possible for the sum of two variables by their
//! individual intervals

use std::collections::{HashMap, HashSet};

use taco_display_utils::join_iterator;

use crate::{
    ActionDefinition,
    expressions::{Atomic, IsDeclared, Variable},
    general_threshold_automaton::{Action, UpdateExpression},
    lia_threshold_automaton::{
        LIARule, LIAThresholdAutomaton, LIAVariableConstraint, SingleAtomConstraint,
        integer_thresholds::{ThresholdCompOp, ThresholdConstraint, WeightedSum},
    },
};

impl LIAThresholdAutomaton {
    /// This function will remove any [`LIAVariableConstraint::SumVarConstraint`]
    /// and replace them with a new variable that is incremented/reset/decremented
    /// when any of its components is incremented, reset, or decremented.
    ///
    /// This is not the most efficient solution for error graphs, but it is the
    /// simplest.
    ///
    /// TODO: replace when more capable interval ordering is ready (see note in
    /// module `no_sum_var` docs)
    pub fn into_ta_without_sum_vars(mut self) -> Self {
        let sv_to_v: HashMap<_, _> = self
            .get_sum_var_constraints()
            .into_iter()
            .map(|v| {
                let v = v.get_atoms().clone();
                let new_var = Self::create_new_variable_for_sumvar(&v, &self);
                (v, new_var)
            })
            .collect();

        self.rules = self
            .rules
            .into_iter()
            .map(|(l, r)| {
                (
                    l,
                    r.into_iter().map(|r| r.remove_sumvar(&sv_to_v)).collect(),
                )
            })
            .collect();
        // new variables start at 0
        self.init_variable_constr.extend(sv_to_v.values().map(|v| {
            let sa = SingleAtomConstraint::new(
                v.clone(),
                ThresholdConstraint::new(ThresholdCompOp::Lt, WeightedSum::new_empty(), 1),
            );

            LIAVariableConstraint::SingleVarConstraint(sa)
        }));
        self.additional_vars_for_sums
            .extend(sv_to_v.into_iter().map(|(sv, v)| (v, sv)));

        self
    }

    /// Get the helper variables that have been added to replace sums of variables
    pub fn get_replacement_vars_for_sumvars(&self) -> &HashMap<Variable, WeightedSum<Variable>> {
        &self.additional_vars_for_sums
    }

    /// Creates a new unique name for a sum of variables
    fn create_new_variable_for_sumvar(
        s: &WeightedSum<Variable>,
        lta: &LIAThresholdAutomaton,
    ) -> Variable {
        let name: String =
            "sv_".to_string() + &join_iterator(s.get_atoms_appearing().map(|v| v.name()), "_");

        let mut new_var = Variable::new(name.clone());
        let mut i = 0;
        while lta.is_declared(&new_var) {
            new_var = Variable::new(name.clone() + &format!("_{i}"));
            i += 1;
        }

        new_var
    }
}

impl LIARule {
    /// Replace the sums of variables in a rule and add the appropriate actions
    fn remove_sumvar(self, sv_to_v: &HashMap<WeightedSum<Variable>, Variable>) -> Self {
        let guard = self.guard.remove_sumvar(sv_to_v);
        let mut acts = self.actions.clone();
        for sc in sv_to_v.keys() {
            acts.extend(Self::compute_acts_to_add(&self.actions, sc, sv_to_v));
        }

        Self {
            id: self.id,
            source: self.source,
            target: self.target,
            guard,
            actions: acts,
        }
    }

    /// Compute all actions that have to be added for the given set of actions
    /// and the current sums of variables
    fn compute_acts_to_add(
        existing_acts: &[Action],
        sc: &WeightedSum<Variable>,
        sv_to_v: &HashMap<WeightedSum<Variable>, Variable>,
    ) -> HashSet<Action> {
        let mut new_actions = HashSet::new();

        let mut effect = HashMap::new();
        for act in existing_acts {
            if sc.contains(act.variable()) {
                let var = sv_to_v.get(sc).expect("Failed to get sumvar").clone();

                let accumulated_effect = effect.entry(var.clone()).or_insert(0);

                let scale_to_effect = *sc.get_factor(act.variable()).unwrap();

                if !scale_to_effect.is_integer() {
                    unimplemented!(
                        "Failed to scale boundary properly, currently such constraints are unsupported at the moment!"
                    );
                }
                let scale_to_effect: i64 = scale_to_effect.try_into().unwrap();

                match act.update() {
                    UpdateExpression::Inc(i) => {
                        *accumulated_effect += (*i as i64) * scale_to_effect;
                    }
                    UpdateExpression::Dec(i) => *accumulated_effect -= *i as i64 * scale_to_effect,
                    UpdateExpression::Reset => unimplemented!(),
                    UpdateExpression::Unchanged => {}
                }
            }
        }

        for (var, acc_effect) in effect.into_iter().filter(|(_, eff)| eff != &0) {
            if acc_effect < 0 {
                new_actions.insert(Action::new_with_update(
                    var,
                    UpdateExpression::Dec(-acc_effect as u32),
                ));
                continue;
            }

            new_actions.insert(Action::new_with_update(
                var,
                UpdateExpression::Inc((acc_effect) as u32),
            ));
        }

        new_actions
    }
}

impl LIAVariableConstraint {
    /// Replace the [`LIAVariableConstraint::SumVarConstraint`] in a
    /// [`LIAVariableConstraint`] by the appropriate
    /// [`LIAVariableConstraint::SingleVarConstraint`]
    fn remove_sumvar(self, sv_to_v: &HashMap<WeightedSum<Variable>, Variable>) -> Self {
        match self {
            LIAVariableConstraint::SumVarConstraint(sv) => {
                let var = sv_to_v
                    .get(sv.get_atoms())
                    .expect("Missing var in translation")
                    .clone();
                LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
                    var,
                    sv.get_threshold_constraint().clone(),
                ))
            }
            LIAVariableConstraint::BinaryGuard(lhs, bc, rhs) => {
                let lhs = lhs.remove_sumvar(sv_to_v);
                let rhs = rhs.remove_sumvar(sv_to_v);
                LIAVariableConstraint::BinaryGuard(Box::new(lhs), bc, Box::new(rhs))
            }
            s => s,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap, HashSet};

    use crate::{
        expressions::{BooleanConnective, Location, Parameter, Variable},
        general_threshold_automaton::{
            Action, UpdateExpression, builder::GeneralThresholdAutomatonBuilder,
        },
        lia_threshold_automaton::{
            LIARule, LIAThresholdAutomaton, LIAVariableConstraint, SingleAtomConstraint,
            SumAtomConstraint,
            integer_thresholds::{
                ThresholdCompOp, ThresholdConstraint, ThresholdConstraintOver, WeightedSum,
            },
        },
    };

    #[test]
    fn test_remove_sumvar_liata() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .initialize()
            .build();

        let lta = LIAThresholdAutomaton {
            ta: ta.clone(),
            rules: HashMap::from([(
                Location::new("loc1"),
                vec![LIARule {
                    id: 0,
                    source: Location::new("l1"),
                    target: Location::new("l2"),
                    guard: LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                        ThresholdConstraintOver::new(
                            WeightedSum::new(BTreeMap::from([
                                (Variable::new("var1"), 1),
                                (Variable::new("var2"), 2),
                            ])),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Lt,
                                BTreeMap::from([(Parameter::new("n"), 3)]),
                                5,
                            ),
                        ),
                    )),
                    actions: vec![Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    )],
                }],
            )]),
            init_variable_constr: vec![],
            additional_vars_for_sums: HashMap::new(),
        };
        let got_lta = lta.into_ta_without_sum_vars();

        let expected_ta = LIAThresholdAutomaton {
            ta: ta.clone(),
            rules: HashMap::from([(
                Location::new("loc1"),
                vec![LIARule {
                    id: 0,
                    source: Location::new("l1"),
                    target: Location::new("l2"),
                    guard: LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                        ThresholdConstraintOver::new(
                            Variable::new("sv_var1_var2"),
                            ThresholdConstraint::new(
                                ThresholdCompOp::Lt,
                                BTreeMap::from([(Parameter::new("n"), 3)]),
                                5,
                            ),
                        ),
                    )),
                    actions: vec![
                        Action::new_with_update(Variable::new("var1"), UpdateExpression::Inc(1)),
                        Action::new_with_update(
                            Variable::new("sv_var1_var2"),
                            UpdateExpression::Inc(1),
                        ),
                    ],
                }],
            )]),
            init_variable_constr: vec![LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("sv_var1_var2"),
                    ThresholdConstraint::new(ThresholdCompOp::Lt, WeightedSum::new_empty(), 1),
                ),
            )],
            additional_vars_for_sums: HashMap::from([(
                Variable::new("sv_var1_var2"),
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
            )]),
        };

        assert_eq!(
            got_lta, expected_ta,
            "got: {got_lta}\n expected:{expected_ta}"
        )
    }

    #[test]
    fn test_remove_sumvar_liarule() {
        let lia_rule = LIARule {
            id: 0,
            source: Location::new("l1"),
            target: Location::new("l2"),
            guard: LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 2),
                    ])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        BTreeMap::from([(Parameter::new("n"), 3)]),
                        5,
                    ),
                ),
            )),
            actions: vec![Action::new_with_update(
                Variable::new("var1"),
                UpdateExpression::Inc(1),
            )],
        };

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]);

        let got_rule = lia_rule.remove_sumvar(&sv_to_v);

        let expected_rule = LIARule {
            id: 0,
            source: Location::new("l1"),
            target: Location::new("l2"),
            guard: LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
                ThresholdConstraintOver::new(
                    Variable::new("sv_var1_var2"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        BTreeMap::from([(Parameter::new("n"), 3)]),
                        5,
                    ),
                ),
            )),
            actions: vec![
                Action::new_with_update(Variable::new("var1"), UpdateExpression::Inc(1)),
                Action::new_with_update(Variable::new("sv_var1_var2"), UpdateExpression::Inc(1)),
            ],
        };

        assert_eq!(got_rule, expected_rule)
    }

    #[test]
    fn test_remove_sumvar_liarule_bug_c1cs() {
        let lia_rule = LIARule {
            id: 0,
            source: Location::new("l1"),
            target: Location::new("l2"),
            guard: LIAVariableConstraint::True,
            actions: vec![
                Action::new_with_update(Variable::new("nfaulty"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("nsnt1F"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("nsnt1"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("nsnt0"), UpdateExpression::Inc(1)),
                Action::new_with_update(Variable::new("nsnt0F"), UpdateExpression::Unchanged),
            ],
        };

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("nsnt0F"), 1),
                (Variable::new("nsnt0"), 1),
            ])),
            Variable::new("sv_nsnt0_nsnt0F"),
        )]);

        let got_rule = lia_rule.remove_sumvar(&sv_to_v);

        let expected_rule = LIARule {
            id: 0,
            source: Location::new("l1"),
            target: Location::new("l2"),
            guard: LIAVariableConstraint::True,
            actions: vec![
                Action::new_with_update(Variable::new("nfaulty"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("nsnt1F"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("nsnt1"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("nsnt0"), UpdateExpression::Inc(1)),
                Action::new_with_update(Variable::new("nsnt0F"), UpdateExpression::Unchanged),
                Action::new_with_update(Variable::new("sv_nsnt0_nsnt0F"), UpdateExpression::Inc(1)),
            ],
        };

        assert_eq!(got_rule, expected_rule)
    }

    #[test]
    fn test_compute_acts_to_add_inc() {
        let acts = vec![Action::new_with_update(
            Variable::new("var1"),
            UpdateExpression::Inc(1),
        )];

        let sc = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]);

        let got_acts = LIARule::compute_acts_to_add(&acts, &sc, &sv_to_v);

        let expected_acts = HashSet::from([Action::new_with_update(
            Variable::new("sv_var1_var2"),
            UpdateExpression::Inc(1),
        )]);

        assert_eq!(got_acts, expected_acts)
    }

    #[test]
    fn test_compute_acts_to_add_dec() {
        let acts = vec![Action::new_with_update(
            Variable::new("var1"),
            UpdateExpression::Dec(2),
        )];

        let sc = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]);

        let got_acts = LIARule::compute_acts_to_add(&acts, &sc, &sv_to_v);

        let expected_acts = HashSet::from([Action::new_with_update(
            Variable::new("sv_var1_var2"),
            UpdateExpression::Dec(2),
        )]);

        assert_eq!(got_acts, expected_acts)
    }

    #[test]
    fn test_compute_acts_to_add_none() {
        let acts = vec![Action::new_with_update(
            Variable::new("var1"),
            UpdateExpression::Unchanged,
        )];

        let sc = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]);

        let got_acts = LIARule::compute_acts_to_add(&acts, &sc, &sv_to_v);

        let expected_acts = HashSet::from([]);

        assert_eq!(got_acts, expected_acts)
    }

    #[test]
    fn test_compute_acts_to_add_diff_var() {
        let acts = vec![Action::new_with_update(
            Variable::new("var3"),
            UpdateExpression::Inc(1),
        )];

        let sc = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]);

        let got_acts = LIARule::compute_acts_to_add(&acts, &sc, &sv_to_v);

        let expected_acts = HashSet::from([]);

        assert_eq!(got_acts, expected_acts)
    }

    #[test]
    fn test_compute_acts_to_add_two_add() {
        let acts = vec![
            Action::new_with_update(Variable::new("var1"), UpdateExpression::Inc(1)),
            Action::new_with_update(Variable::new("var2"), UpdateExpression::Inc(1)),
        ];

        let sc = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        let sv_to_v = HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]);

        let got_acts = LIARule::compute_acts_to_add(&acts, &sc, &sv_to_v);

        let expected_acts = HashSet::from([Action::new_with_update(
            Variable::new("sv_var1_var2"),
            UpdateExpression::Inc(3),
        )]);

        assert_eq!(got_acts, expected_acts)
    }

    #[test]
    fn test_remove_sumvar_var_constr() {
        let thr = LIAVariableConstraint::False;
        let got_thr = thr.remove_sumvar(&HashMap::new());
        let expected = LIAVariableConstraint::False;
        assert_eq!(got_thr, expected);

        let thr = LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
            ThresholdConstraintOver::new(
                WeightedSum::new(BTreeMap::from([
                    (Variable::new("var1"), 1),
                    (Variable::new("var2"), 2),
                ])),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    5,
                ),
            ),
        ));
        let got_thr = thr.remove_sumvar(&HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]));
        let expected = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint(
            ThresholdConstraintOver::new(
                Variable::new("sv_var1_var2"),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    BTreeMap::from([(Parameter::new("n"), 3)]),
                    5,
                ),
            ),
        ));
        assert_eq!(got_thr, expected);

        let thr = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SumVarConstraint(SumAtomConstraint(
                ThresholdConstraintOver::new(
                    WeightedSum::new(BTreeMap::from([
                        (Variable::new("var1"), 1),
                        (Variable::new("var2"), 2),
                    ])),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        BTreeMap::from([(Parameter::new("n"), 3)]),
                        5,
                    ),
                ),
            ))),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::True),
        );
        let got_thr = thr.remove_sumvar(&HashMap::from([(
            WeightedSum::new(BTreeMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
            ])),
            Variable::new("sv_var1_var2"),
        )]));
        let expected = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint(ThresholdConstraintOver::new(
                    Variable::new("sv_var1_var2"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        BTreeMap::from([(Parameter::new("n"), 3)]),
                        5,
                    ),
                )),
            )),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::True),
        );
        assert_eq!(got_thr, expected);
    }
}

//! This module contains the logic to transform a general boolean expression
//! over variables into a [`super::LIAVariableConstraint`].
//!
//! The conversion generally works as described in
//! [`../general_to_lia.rs`](general_to_lia.rs).
//!
//! This module implements the logic that after successfully splitting the
//! expression into pairs of atoms and rational factors, brings all variables to
//! the left and collects all parameter factor pairs and constants on the right.
//!
//! Then the module converts them into the appropriate [`LIAVariableConstraint`]
//! type, i.e., either a [`SingleAtomConstraint`], [`SumAtomConstraint`] or
//! [`ComparisonConstraint`].

use std::{collections::HashMap, hash::Hash};

use crate::{
    BooleanVarConstraint,
    expressions::{
        Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Variable,
        fraction::Fraction,
    },
    lia_threshold_automaton::{
        ComparisonConstraint, LIAVariableConstraint, SingleAtomConstraint, SumAtomConstraint,
        integer_thresholds::{
            IntoNoDivBooleanExpr, Threshold, ThresholdCompOp, ThresholdConstraint,
        },
    },
};

use super::{ConstraintRewriteError, remove_boolean_neg::NonNegatedBooleanExpression};

impl TryFrom<&BooleanVarConstraint> for LIAVariableConstraint {
    type Error = ConstraintRewriteError;

    fn try_from(expr: &BooleanExpression<Variable>) -> Result<Self, Self::Error> {
        let non_negated = expr.remove_boolean_negations();
        non_negated.try_into()
    }
}

impl TryFrom<BooleanVarConstraint> for LIAVariableConstraint {
    type Error = ConstraintRewriteError;

    fn try_from(expr: BooleanExpression<Variable>) -> Result<Self, Self::Error> {
        (&expr).try_into()
    }
}

impl TryFrom<NonNegatedBooleanExpression<Variable>> for LIAVariableConstraint {
    type Error = ConstraintRewriteError;
    /// Parse the `NonNegatedBooleanExpression` into a LIAVariableConstraint by
    /// converting into weighted sums of parameters and variables
    fn try_from(value: NonNegatedBooleanExpression<Variable>) -> Result<Self, Self::Error> {
        match value {
            NonNegatedBooleanExpression::True => Ok(LIAVariableConstraint::True),
            NonNegatedBooleanExpression::False => Ok(LIAVariableConstraint::False),
            NonNegatedBooleanExpression::BinaryExpression(lhs, op, rhs) => {
                let lhs = (*lhs).try_into()?;
                let rhs = (*rhs).try_into()?;

                Ok(LIAVariableConstraint::BinaryGuard(
                    Box::new(lhs),
                    op,
                    Box::new(rhs),
                ))
            }
            NonNegatedBooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                canonicalize_comp_op(*lhs, op, *rhs)
            }
        }
    }
}

/// Translate the constraints into constraints over the canonical thresholds
fn canonicalize_comp_op(
    lhs: IntegerExpression<Variable>,
    op: ComparisonOp,
    rhs: IntegerExpression<Variable>,
) -> Result<LIAVariableConstraint, ConstraintRewriteError> {
    // Catch trivially true or false constraints and replace them
    if let Ok(res) =
        BooleanExpression::ComparisonExpression(Box::new(lhs.clone()), op, Box::new(rhs.clone()))
            .check_satisfied(&HashMap::new(), &HashMap::new())
    {
        if res {
            return Ok(LIAVariableConstraint::True);
        }
        return Ok(LIAVariableConstraint::False);
    }

    match op {
        ComparisonOp::Gt => {
            let op = ThresholdCompOp::Geq;
            let lhs = lhs - IntegerExpression::Const(1);

            let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
            let thr_c = ThresholdConstraint::new_from_thr(op, thr);
            parse_guard_type(variables, thr_c)
        }
        ComparisonOp::Geq => {
            let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
            let thr_c = ThresholdConstraint::new_from_thr(ThresholdCompOp::Geq, thr);
            parse_guard_type(variables, thr_c)
        }
        ComparisonOp::Leq => {
            let op = ThresholdCompOp::Lt;
            let rhs = rhs + IntegerExpression::Const(1);

            let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
            let thr_c = ThresholdConstraint::new_from_thr(op, thr);

            parse_guard_type(variables, thr_c)
        }
        ComparisonOp::Lt => {
            let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
            let thr_c = ThresholdConstraint::new_from_thr(ThresholdCompOp::Lt, thr);
            parse_guard_type(variables, thr_c)
        }
        ComparisonOp::Eq => {
            let lower_constr = canonicalize_comp_op(lhs.clone(), ComparisonOp::Leq, rhs.clone())?;
            let upper_constr = canonicalize_comp_op(lhs.clone(), ComparisonOp::Geq, rhs.clone())?;

            Ok(LIAVariableConstraint::BinaryGuard(
                Box::new(lower_constr),
                BooleanConnective::And,
                Box::new(upper_constr),
            ))
        }
        ComparisonOp::Neq => {
            let lower_constr = canonicalize_comp_op(lhs.clone(), ComparisonOp::Lt, rhs.clone())?;
            let upper_constr = canonicalize_comp_op(lhs.clone(), ComparisonOp::Gt, rhs.clone())?;

            Ok(LIAVariableConstraint::BinaryGuard(
                Box::new(lower_constr),
                BooleanConnective::Or,
                Box::new(upper_constr),
            ))
        }
    }
}

/// This function is designed to rewrite an comparison expression into a form
/// where the returned `HashMap<T, Fraction>` forms the new lhs of the equation
/// and the returned threshold is the right hand side of the equation
///
// TODO: Refactor: remove the pub(crate)
pub(crate) fn split_pairs_into_atom_and_threshold<T: Atomic>(
    lhs: IntegerExpression<T>,
    rhs: IntegerExpression<T>,
) -> Result<(HashMap<T, Fraction>, Threshold), ConstraintRewriteError> {
    let lhs = lhs
        .remove_unary_neg_and_sub()
        .remove_div()?
        .split_into_factor_pairs()?;

    let rhs = rhs
        .remove_unary_neg_and_sub()
        .remove_div()?
        .split_into_factor_pairs()?;

    let atoms = combine_pair_iterators(lhs.get_atom_factor_pairs(), rhs.get_atom_factor_pairs());

    let params = combine_pair_iterators(rhs.get_param_factor_pairs(), lhs.get_param_factor_pairs());

    let c = rhs.get_const_factor() - lhs.get_const_factor();
    let t = Threshold::new(params, c);

    Ok((atoms, t))
}

fn parse_guard_type(
    vars: HashMap<Variable, Fraction>,
    thr_c: ThresholdConstraint,
) -> Result<LIAVariableConstraint, ConstraintRewriteError> {
    if vars.is_empty() {
        // We have caught expressions over only constants in `canonicalize_comp_op`
        //
        // The evaluation will fail if the constraint contains parameters
        // This would mean that the variable expression constraints the
        // parameters which is not permitted !
        return Err(ConstraintRewriteError::ParameterConstraint(Box::new(
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Const(0)),
                thr_c.get_op().into(),
                Box::new(thr_c.get_threshold().get_scaled_integer_expression(1)),
            ),
        )));
    }

    if vars.len() == 1 {
        let (var, factor) = vars.into_iter().next().unwrap();
        let mut thr = thr_c;
        thr.scale(factor.inverse());

        let svar_guard = SingleAtomConstraint::new(var, thr);

        return Ok(LIAVariableConstraint::SingleVarConstraint(svar_guard));
    }

    if let Ok(g) = SumAtomConstraint::try_new(vars.clone(), thr_c.clone()) {
        return Ok(LIAVariableConstraint::SumVarConstraint(g));
    }

    Ok(LIAVariableConstraint::ComparisonConstraint(
        ComparisonConstraint::try_new(vars, thr_c).expect("Failed to categorize guard type."),
    ))
}

/// Combine two iterators over pairs of tuples over (T, Fraction) into a single
/// map from T to [`Fraction`], where all entries from `negated_it` are inserted
/// negated
fn combine_pair_iterators<'a, T: Clone + Eq + Hash + 'a>(
    reg_it: impl Iterator<Item = (&'a T, &'a Fraction)>,
    negated_it: impl Iterator<Item = (&'a T, &'a Fraction)>,
) -> HashMap<T, Fraction> {
    reg_it
        .map(|(t, f)| (t.clone(), *f))
        // negate the all factors from `negated_it` and add them to the chain
        .chain(negated_it.map(|(t, f)| (t.clone(), -*f)))
        .fold(HashMap::new(), |mut acc, (p, f)| {
            // if key exists, add the factor, otherwise insert it
            acc.entry(p).and_modify(|e| *e += f).or_insert(f);

            acc
        })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{
        expressions::{
            BooleanConnective, ComparisonOp, IntegerExpression, Parameter, Variable,
            fraction::Fraction,
        },
        lia_threshold_automaton::{
            ConstraintRewriteError, LIAVariableConstraint, SingleAtomConstraint, SumAtomConstraint,
            general_to_lia::remove_boolean_neg::NonNegatedBooleanExpression,
            integer_thresholds::{ThresholdCompOp, ThresholdConstraint},
        },
    };

    #[test]
    fn test_try_into_single_var() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("var"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(0)),
        );

        let expected_expr = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 1),
        ));
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_single_var_eq() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("var"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let expected_expr = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("var"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(Parameter, Fraction)>::new(),
                        1,
                    ),
                ),
            )),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("var"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(Parameter, Fraction)>::new(),
                        0,
                    ),
                ),
            )),
        );
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_single_var_neq() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("var"))),
            ComparisonOp::Neq,
            Box::new(IntegerExpression::Const(1)),
        );

        let expected_expr = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("var"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Lt,
                        Vec::<(Parameter, Fraction)>::new(),
                        1,
                    ),
                ),
            )),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::SingleVarConstraint(
                SingleAtomConstraint::new(
                    Variable::new("var"),
                    ThresholdConstraint::new(
                        ThresholdCompOp::Geq,
                        Vec::<(Parameter, Fraction)>::new(),
                        2,
                    ),
                ),
            )),
        );
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_single_var_scale_factor_correct() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(2) * IntegerExpression::Atom(Variable::new("var"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(7)),
        );

        let expected_expr = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 4),
        ));
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_simple_guards() {
        let expr: NonNegatedBooleanExpression<Variable> = NonNegatedBooleanExpression::True;
        let expected = LIAVariableConstraint::True;

        let result = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(result, expected);

        let expr: NonNegatedBooleanExpression<Variable> = NonNegatedBooleanExpression::False;
        let expected = LIAVariableConstraint::False;

        let result = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_binary_guard() {
        // top && top
        let expr = NonNegatedBooleanExpression::BinaryExpression(
            Box::new(NonNegatedBooleanExpression::True),
            BooleanConnective::And,
            Box::new(NonNegatedBooleanExpression::True),
        );

        let expected_expr = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::True),
            BooleanConnective::And,
            Box::new(LIAVariableConstraint::True),
        );
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);

        //bot || top
        let expr = NonNegatedBooleanExpression::BinaryExpression(
            Box::new(NonNegatedBooleanExpression::False),
            BooleanConnective::Or,
            Box::new(NonNegatedBooleanExpression::True),
        );

        let expected_expr = LIAVariableConstraint::BinaryGuard(
            Box::new(LIAVariableConstraint::False),
            BooleanConnective::Or,
            Box::new(LIAVariableConstraint::True),
        );
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_single_var_double_var_lhs() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(
                IntegerExpression::Atom(Variable::new("var"))
                    + IntegerExpression::Atom(Variable::new("var")),
            ),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );

        let expected_expr = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var"),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                Vec::<(Parameter, Fraction)>::new(),
                Fraction::new(2, 2, false),
            ),
        ));
        // TODO: consider whether this is fine
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_single_var_double_var_rhs() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(1)),
            ComparisonOp::Leq,
            Box::new(
                IntegerExpression::Atom(Variable::new("var"))
                    + IntegerExpression::Atom(Variable::new("var")),
            ),
        );
        let expected_expr = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var"),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                Vec::<(Parameter, Fraction)>::new(),
                Fraction::new(1, 2, false),
            ),
        ));
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);

        // TODO: consider whether this is fine
        // 1 < 2 var --> 2var > 1 --> var >= 1
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(1)),
            ComparisonOp::Lt,
            Box::new(
                IntegerExpression::Atom(Variable::new("var"))
                    + IntegerExpression::Atom(Variable::new("var")),
            ),
        );
        let expected_expr = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var"),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                Vec::<(Parameter, Fraction)>::new(),
                Fraction::new(1, 1, false),
            ),
        ));
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);

        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(6) - IntegerExpression::Atom(Variable::new("var"))),
            ComparisonOp::Leq,
            Box::new(
                IntegerExpression::Atom(Variable::new("var"))
                    + IntegerExpression::Atom(Variable::new("var")),
            ),
        );
        let expected_expr = LIAVariableConstraint::SingleVarConstraint(SingleAtomConstraint::new(
            Variable::new("var"),
            ThresholdConstraint::new(
                ThresholdCompOp::Geq,
                Vec::<(Parameter, Fraction)>::new(),
                Fraction::new(2, 1, false),
            ),
        ));
        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_multi_var() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(
                IntegerExpression::Atom(Variable::new("var1"))
                    + IntegerExpression::Atom(Variable::new("var2")),
            ),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(0)),
        );

        let expected_expr = LIAVariableConstraint::SumVarConstraint(
            SumAtomConstraint::try_new(
                BTreeMap::from([(Variable::new("var1"), 1), (Variable::new("var2"), 1)]),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    0,
                ),
            )
            .unwrap(),
        );

        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_multi_var_double_var_lhs() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(
                IntegerExpression::Atom(Variable::new("var1"))
                    + IntegerExpression::Atom(Variable::new("var2"))
                    + IntegerExpression::Atom(Variable::new("var1")) * IntegerExpression::Const(2),
            ),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(0)),
        );

        let expected_expr = LIAVariableConstraint::SumVarConstraint(
            SumAtomConstraint::try_new(
                BTreeMap::from([(Variable::new("var1"), 3), (Variable::new("var2"), 1)]),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    0,
                ),
            )
            .unwrap(),
        );

        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_multi_var_double_var_rhs() {
        // var1 + var2 + 5 * var1 <  0 + 2 * var1
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(
                IntegerExpression::Atom(Variable::new("var1"))
                    + IntegerExpression::Atom(Variable::new("var2"))
                    + IntegerExpression::Atom(Variable::new("var1")) * IntegerExpression::Const(5),
            ),
            ComparisonOp::Lt,
            Box::new(
                IntegerExpression::Const(0)
                    + (IntegerExpression::Atom(Variable::new("var1"))
                        * IntegerExpression::Const(2)),
            ),
        );

        let expected_expr = LIAVariableConstraint::SumVarConstraint(
            SumAtomConstraint::try_new(
                BTreeMap::from([(Variable::new("var1"), 4), (Variable::new("var2"), 1)]),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    0,
                ),
            )
            .unwrap(),
        );

        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_comp_guard() {
        // var1 + var2 + 2 * var1 <  0 + 5 * var1
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(
                IntegerExpression::Atom(Variable::new("var1"))
                    + IntegerExpression::Atom(Variable::new("var2"))
                    + IntegerExpression::Atom(Variable::new("var1")) * IntegerExpression::Const(2),
            ),
            ComparisonOp::Lt,
            Box::new(
                IntegerExpression::Const(0)
                    + (IntegerExpression::Atom(Variable::new("var1"))
                        * IntegerExpression::Const(5)),
            ),
        );

        let expected_expr = LIAVariableConstraint::ComparisonConstraint(
            crate::lia_threshold_automaton::ComparisonConstraint::try_new(
                BTreeMap::from([
                    (Variable::new("var1"), -Fraction::from(2)),
                    (Variable::new("var2"), 1.into()),
                ]),
                ThresholdConstraint::new(
                    ThresholdCompOp::Lt,
                    Vec::<(Parameter, Fraction)>::new(),
                    0,
                ),
            )
            .unwrap(),
        );

        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_try_into_only_const() {
        // 0 == 0
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(0)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let expected_expr = LIAVariableConstraint::True;

        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);

        // 0 < 0
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(0)),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(0)),
        );

        let expected_expr = LIAVariableConstraint::False;

        let got = LIAVariableConstraint::try_from(expr).unwrap();
        assert_eq!(got, expected_expr);
    }

    #[test]
    fn test_error_on_parameter_constraint() {
        let expr = NonNegatedBooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(0)),
        );

        let got = LIAVariableConstraint::try_from(expr);
        assert!(got.is_err(), "Got {got:?}");
        assert!(matches!(
            got,
            Err(ConstraintRewriteError::ParameterConstraint(_))
        ));
    }
}

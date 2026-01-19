//! Logic to remove boolean negations from an expression
//!
//! This module defines the new type [`NonNegatedBooleanExpression`] which is a
//! restricted variant of boolean expressions, as it does not allow for boolean
//! negations, that is the `!` operator is not allowed.
//!
//! Every [`BooleanExpression`] can be converted into a
//! `NonNegatedBooleanExpression`, as the negations can be removed by pushing
//! them into the formula, potentially negating inner comparison expressions.

use std::fmt::{Debug, Display};

use crate::expressions::{
    Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression,
};

impl<T: Atomic> BooleanExpression<T> {
    /// Remove boolean negations from an expression, transforming the expression
    /// into a `NonNegatedBooleanExpression`.
    ///
    /// This function removes a boolean negation by pushing it inwards and
    /// transforming the expression accordingly.
    ///
    /// # Example
    ///
    /// ```rust, ignore
    /// // !(x > 0)
    /// let expr = BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
    ///    Box::new(IntegerExpression::Atom(Variable::new("x"))),
    ///    ComparisonOp::Gt,
    ///    Box::new(IntegerExpression::Const(0)),
    /// )));
    ///
    /// // !(x > 0) -> x <= 0
    /// let transformed_expr = expr.remove_boolean_negations();
    ///
    /// assert_eq!(
    ///    transformed_expr,
    ///    NonNegatedBooleanExpression::ComparisonExpression(
    ///         Box::new(IntegerExpression::Atom(Variable::new("x"))),
    ///         ComparisonOp::Leq,
    ///         Box::new(IntegerExpression::Const(0)),
    ///    ),
    /// );
    /// ```
    ///
    /// # Implementation
    ///
    /// The goal of this function is to remove all boolean negations from an
    /// expression. This is done by recursively traversing the expression, if a
    /// negation i.e. `Not` is encountered, the negation is pushed inwards using
    /// the helper function `negate_expression`.
    ///
    /// The helper function then:
    ///     - replaces a [`BooleanExpression::True`] constant with a
    ///       [`BooleanExpression::False`] and vice versa
    ///     - calls [`BooleanExpression::remove_boolean_negations`] again if
    ///       another [`BooleanExpression::Not`] is encountered (double negation)
    ///     - inverts the comparison operator if a comparison expression is
    ///       encountered
    ///     - inverts the boolean connective if a binary expression is encountered
    ///       and continues recursively on the left and right side of the
    ///       binary expression
    pub fn remove_boolean_negations(&self) -> NonNegatedBooleanExpression<T> {
        match self {
            BooleanExpression::ComparisonExpression(lhs, comparison_op, rhs) => {
                NonNegatedBooleanExpression::ComparisonExpression(
                    lhs.clone(),
                    *comparison_op,
                    rhs.clone(),
                )
            }
            BooleanExpression::True => NonNegatedBooleanExpression::True,
            BooleanExpression::False => NonNegatedBooleanExpression::False,
            BooleanExpression::BinaryExpression(lhs, op, rhs) => {
                NonNegatedBooleanExpression::BinaryExpression(
                    Box::new(lhs.remove_boolean_negations()),
                    *op,
                    Box::new(rhs.remove_boolean_negations()),
                )
            }
            BooleanExpression::Not(inner_expr) => inner_expr.negate_expression(),
        }
    }

    /// Computes the negation of an expression and removes any inner negations.
    ///
    /// Helper function for [`BooleanExpression::remove_boolean_negations`],
    /// called when a negation is encountered to remove it by pushing it
    /// inwards.
    fn negate_expression(&self) -> NonNegatedBooleanExpression<T> {
        match self {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                NonNegatedBooleanExpression::ComparisonExpression(
                    lhs.clone(),
                    op.invert(),
                    rhs.clone(),
                )
            }
            BooleanExpression::BinaryExpression(lhs, op, rhs) => {
                NonNegatedBooleanExpression::BinaryExpression(
                    Box::new(lhs.negate_expression()),
                    op.invert(),
                    Box::new(rhs.negate_expression()),
                )
            }
            BooleanExpression::Not(ex) => ex.remove_boolean_negations(),
            BooleanExpression::True => NonNegatedBooleanExpression::False,
            BooleanExpression::False => NonNegatedBooleanExpression::True,
        }
    }
}

impl<T: Atomic> From<BooleanExpression<T>> for NonNegatedBooleanExpression<T> {
    fn from(val: BooleanExpression<T>) -> Self {
        val.remove_boolean_negations()
    }
}

/// Boolean expressions that do not contain a `Not`
#[derive(Debug, PartialEq, Clone)]
pub enum NonNegatedBooleanExpression<T: Atomic> {
    /// Comparison between two integer expressions
    ComparisonExpression(
        Box<IntegerExpression<T>>,
        ComparisonOp,
        Box<IntegerExpression<T>>,
    ),
    /// Boolean expressions combined through boolean connective
    BinaryExpression(
        Box<NonNegatedBooleanExpression<T>>,
        BooleanConnective,
        Box<NonNegatedBooleanExpression<T>>,
    ),
    /// true
    True,
    /// false
    False,
}

impl<T: Atomic> Display for NonNegatedBooleanExpression<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NonNegatedBooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                write!(f, "{lhs} {op} {rhs}")
            }
            NonNegatedBooleanExpression::BinaryExpression(lhs, op, rhs) => {
                write!(f, "({lhs}) {op} ({rhs})")
            }
            NonNegatedBooleanExpression::True => write!(f, "true"),
            NonNegatedBooleanExpression::False => write!(f, "false"),
        }
    }
}

#[cfg(test)]
mod test {
    // This set of tests uses a private interface, therefore might be removed
    // However, they are extremely useful for debugging.
    mod tests_remove_boolean_negations {

        use crate::{
            expressions::{
                BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Variable,
            },
            lia_threshold_automaton::general_to_lia::remove_boolean_neg::NonNegatedBooleanExpression,
        };

        #[test]
        fn test_remove_negation_comparison_expression1() {
            let expr = BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Variable::new("y"))),
            )));
            let expected_expr = NonNegatedBooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Atom(Variable::new("y"))),
            );

            let got_expr = expr.remove_boolean_negations();

            assert_eq!(got_expr, expected_expr);
        }

        #[test]
        fn test_remove_negation_comparison_expression2() {
            let expr = BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(1)),
            )));
            let expected_expr = NonNegatedBooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            );

            let got_expr = expr.remove_boolean_negations();

            assert_eq!(got_expr, expected_expr);
        }

        #[test]
        fn test_remove_negation_boolean_con_inner() {
            let expr = BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::Not(Box::new(
                    BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("x"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(5)),
                    ),
                ))),
                BooleanConnective::And,
                Box::new(BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Leq,
                    Box::new(IntegerExpression::Atom(Variable::new("z"))),
                )),
            );

            let expected_expr = NonNegatedBooleanExpression::BinaryExpression(
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Leq,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::And,
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Leq,
                    Box::new(IntegerExpression::Atom(Variable::new("z"))),
                )),
            );

            let got_expr = expr.remove_boolean_negations();

            assert_eq!(got_expr, expected_expr);
        }

        #[test]
        fn test_remove_negation_boolean_con_outer() {
            let expr = BooleanExpression::Not(Box::new(BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::Or,
                Box::new(BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Atom(Variable::new("z"))),
                )),
            )));

            let expected_expr = NonNegatedBooleanExpression::BinaryExpression(
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::And,
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Atom(Variable::new("z"))),
                )),
            );

            let got_expr = expr.remove_boolean_negations();

            assert_eq!(got_expr, expected_expr);
        }

        #[test]
        fn test_remove_negation_boolean_con_outer_and_inner() {
            let expr = BooleanExpression::Not(Box::new(BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::Not(Box::new(BooleanExpression::Not(
                    Box::new(BooleanExpression::Not(Box::new(
                        BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("x"))),
                            ComparisonOp::Neq,
                            Box::new(IntegerExpression::Const(5)),
                        ),
                    ))),
                )))),
                BooleanConnective::And,
                Box::new(BooleanExpression::Not(Box::new(BooleanExpression::Not(
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("y"))),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::Atom(Variable::new("z"))),
                    )),
                )))),
            )));

            let expected_expr = NonNegatedBooleanExpression::BinaryExpression(
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::Or,
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Atom(Variable::new("z"))),
                )),
            );

            let got_expr = NonNegatedBooleanExpression::<Variable>::from(expr);

            assert_eq!(got_expr, expected_expr);
        }

        #[test]
        fn test_remove_negation_constants() {
            let expr: BooleanExpression<Variable> = BooleanExpression::True;
            assert_eq!(
                NonNegatedBooleanExpression::<Variable>::from(expr),
                NonNegatedBooleanExpression::True
            );

            let expr = BooleanExpression::<Variable>::False;
            assert_eq!(
                NonNegatedBooleanExpression::<Variable>::from(expr),
                NonNegatedBooleanExpression::False
            );

            let expr = BooleanExpression::Not(Box::new(BooleanExpression::<Variable>::True));
            assert_eq!(
                NonNegatedBooleanExpression::<Variable>::from(expr),
                NonNegatedBooleanExpression::False
            );

            let expr = BooleanExpression::Not(Box::new(BooleanExpression::<Variable>::False));
            assert_eq!(
                NonNegatedBooleanExpression::<Variable>::from(expr),
                NonNegatedBooleanExpression::True
            );
        }

        #[test]
        fn test_display_non_negated_boolean_expression() {
            let expr = NonNegatedBooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(5)),
            );

            let expected_str = "x == 5";
            assert_eq!(expr.to_string(), expected_str);

            let expr = NonNegatedBooleanExpression::BinaryExpression(
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(5)),
                )),
                BooleanConnective::And,
                Box::new(NonNegatedBooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("y"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(3)),
                )),
            );

            let expected_str = "(x == 5) && (y != 3)";
            assert_eq!(expr.to_string(), expected_str);

            let expr: NonNegatedBooleanExpression<Variable> = NonNegatedBooleanExpression::True;
            let expected_str = "true";
            assert_eq!(expr.to_string(), expected_str);

            let expr: NonNegatedBooleanExpression<Variable> = NonNegatedBooleanExpression::False;
            let expected_str = "false";
            assert_eq!(expr.to_string(), expected_str);
        }
    }
}

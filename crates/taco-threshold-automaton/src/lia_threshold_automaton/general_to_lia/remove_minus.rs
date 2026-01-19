//! Remove unary negations and subtractions from integer expressions
//!
//! This module defines a new type [`NonMinusIntegerExpr`] that represents a
//! restricted integer expression which does not contain the sub operator
//! nor unary negations. However, it does have support for negated constants.
//!
//! Any [`IntegerExpression`] can be converted into a [`NonMinusIntegerExpr`],
//! by pushing the negation inwards until they can be applied to a constant or
//! until a factor of -1 can be added to an atom.

use std::fmt::{Debug, Display};

use crate::expressions::{Atomic, IntegerExpression, IntegerOp, Parameter};

/// Integer expression that does not contain a minus operator, i.e., no negations
/// or subtractions, only negated constants are allowed.
#[derive(Debug, PartialEq, Clone)]
pub enum NonMinusIntegerExpr<T: Atomic> {
    /// Atomic of type T
    Atom(T),
    /// Integer constant
    Const(u32),
    /// Negated integer constant
    NegConst(u32),
    /// Parameter
    Param(Parameter),
    /// Integer expression combining two Integer expressions through an
    /// arithmetic operator
    BinaryExpr(
        Box<NonMinusIntegerExpr<T>>,
        NonMinusIntegerOp,
        Box<NonMinusIntegerExpr<T>>,
    ),
}

impl<T: Atomic> From<IntegerExpression<T>> for NonMinusIntegerExpr<T> {
    fn from(val: IntegerExpression<T>) -> Self {
        val.remove_unary_neg_and_sub()
    }
}

impl<T: Atomic> Display for NonMinusIntegerExpr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NonMinusIntegerExpr::Atom(atom) => write!(f, "{atom}"),
            NonMinusIntegerExpr::Const(c) => write!(f, "{c}"),
            NonMinusIntegerExpr::NegConst(c) => write!(f, "-{c}"),
            NonMinusIntegerExpr::Param(param) => write!(f, "{param}"),
            NonMinusIntegerExpr::BinaryExpr(lhs, op, rhs) => {
                write!(f, "({lhs} {op} {rhs})")
            }
        }
    }
}

/// Arithmetic operators without -
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum NonMinusIntegerOp {
    /// +
    Add,
    /// *
    Mul,
    /// /
    Div,
}

impl From<IntegerOp> for NonMinusIntegerOp {
    /// Convert an [`IntegerOp`] to a NonMinusIntegerOp
    ///
    /// Panics if the [`IntegerOp`] is a subtraction operator
    fn from(op: IntegerOp) -> Self {
        match op {
            IntegerOp::Add => NonMinusIntegerOp::Add,
            IntegerOp::Mul => NonMinusIntegerOp::Mul,
            IntegerOp::Div => NonMinusIntegerOp::Div,
            IntegerOp::Sub => unreachable!("Subtraction should have been removed"),
        }
    }
}

impl From<NonMinusIntegerOp> for IntegerOp {
    fn from(op: NonMinusIntegerOp) -> Self {
        match op {
            NonMinusIntegerOp::Add => IntegerOp::Add,
            NonMinusIntegerOp::Mul => IntegerOp::Mul,
            NonMinusIntegerOp::Div => IntegerOp::Div,
        }
    }
}

impl Display for NonMinusIntegerOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NonMinusIntegerOp::Add => write!(f, "+"),
            NonMinusIntegerOp::Mul => write!(f, "*"),
            NonMinusIntegerOp::Div => write!(f, "/"),
        }
    }
}

impl<T: Atomic> IntegerExpression<T> {
    /// Remove unary negations and subtractions from the integer expression
    /// such that there are only negated constants.
    ///
    /// # Implementation
    ///
    /// The function recursively traverses the expression tree and pushes
    /// negations inwards until they are in front of constants, atoms, or
    /// parameters. In the latter two cases, it adds a `-1 *` in front of the
    /// atom or parameter.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    ///
    /// // 1 - (n + -5)
    /// let expr = IntegerExpression::BinaryExpr(
    ///     Box::new(IntegerExpression::Const(1)),
    ///     IntegerOp::Sub,
    ///     Box::new(IntegerExpression::BinaryExpr(
    ///         Box::new(IntegerExpression::Param(Parameter::new("n"))),
    ///         IntegerOp::Add,
    ///         Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Const(5)))),
    ///     )),
    /// );
    ///
    /// // 1 + (-1 * n + 5)
    /// let expected_expr : NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
    ///     Box::new(NonMinusIntegerExpr::Const(1)),
    ///     NonMinusIntegerOp::Add,
    ///     Box::new(NonMinusIntegerExpr::BinaryExpr(
    ///         Box::new(
    ///             NonMinusIntegerExpr::BinaryExpr(
    ///                 Box::new(NonMinusIntegerExpr::NegConst(1)),
    ///                 NonMinusIntegerOp::Mul,
    ///                 Box::new(NonMinusIntegerExpr::Param(Parameter::new("n"))),
    ///            )
    ///         ),
    ///         NonMinusIntegerOp::Add,
    ///         Box::new(NonMinusIntegerExpr::Const(5)),
    ///     )),
    /// );
    ///     
    /// let got_expr = expr.remove_unary_neg_and_sub();
    /// assert_eq!(got_expr, expected_expr);
    /// ```
    pub fn remove_unary_neg_and_sub(self) -> NonMinusIntegerExpr<T> {
        match self {
            IntegerExpression::Const(c) => NonMinusIntegerExpr::Const(c),
            IntegerExpression::Param(p) => NonMinusIntegerExpr::Param(p),
            IntegerExpression::Atom(a) => NonMinusIntegerExpr::Atom(a),
            IntegerExpression::Neg(ex) => ex.negate_expression(),
            // Found subtraction, push it inwards on the right hand side
            IntegerExpression::BinaryExpr(lhs, IntegerOp::Sub, rhs) => {
                let lhs = lhs.remove_unary_neg_and_sub();
                let rhs = rhs.negate_expression();
                NonMinusIntegerExpr::BinaryExpr(
                    Box::new(lhs),
                    NonMinusIntegerOp::Add,
                    Box::new(rhs),
                )
            }
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                let lhs = lhs.remove_unary_neg_and_sub();
                let rhs = rhs.remove_unary_neg_and_sub();
                NonMinusIntegerExpr::BinaryExpr(Box::new(lhs), op.into(), Box::new(rhs))
            }
        }
    }

    /// Compute the negation of expression and removes any inner negations or
    /// subtractions
    ///
    /// Helper function for `remove_unary_neg_and_sub`: This function pushes a
    /// found negation inwards until they are in front of constants, atoms, or
    /// parameters. In the latter two cases, it adds a -1 * in front of the
    /// atom or parameter.
    fn negate_expression(self) -> NonMinusIntegerExpr<T> {
        match self {
            IntegerExpression::Const(c) => NonMinusIntegerExpr::NegConst(c),
            IntegerExpression::Param(p) => NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::NegConst(1)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::Param(p)),
            ),
            IntegerExpression::Atom(a) => NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::NegConst(1)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::Atom(a)),
            ),
            // Negation found, apply double negation rule and continue eliminating minus from subexpression
            IntegerExpression::Neg(ex) => ex.remove_unary_neg_and_sub(),
            // Found inner subtraction: negate left hand side and continue eliminating potential negations from right hand side
            IntegerExpression::BinaryExpr(lhs, IntegerOp::Sub, rhs) => {
                let lhs = lhs.negate_expression();
                let rhs = rhs.remove_unary_neg_and_sub();
                NonMinusIntegerExpr::BinaryExpr(
                    Box::new(lhs),
                    NonMinusIntegerOp::Add,
                    Box::new(rhs),
                )
            }
            // Addition: continue pushing negation to both subexpressions
            IntegerExpression::BinaryExpr(lhs, IntegerOp::Add, rhs) => {
                let lhs = lhs.negate_expression();
                let rhs = rhs.negate_expression();
                NonMinusIntegerExpr::BinaryExpr(
                    Box::new(lhs),
                    NonMinusIntegerOp::Add,
                    Box::new(rhs),
                )
            }
            // Multiplication or division: push negation to either lhs or rhs of the expression
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                // To avoid making the expression more complex (by introducing many `-1 *` factors)
                // we check whether lhs or rhs has a negation that can be removed by pushing the negation
                // inwards. If so, we choose the side with the negation.
                if rhs.has_removable_negation_inside(false) {
                    NonMinusIntegerExpr::BinaryExpr(
                        Box::new(lhs.remove_unary_neg_and_sub()),
                        op.into(),
                        Box::new(rhs.negate_expression()),
                    )
                } else {
                    NonMinusIntegerExpr::BinaryExpr(
                        Box::new(lhs.negate_expression()),
                        op.into(),
                        Box::new(rhs.remove_unary_neg_and_sub()),
                    )
                }
            }
        }
    }

    /// Check whether further down the expression tree there is a negation
    /// that will be removed if we push the negation inwards.
    ///
    /// Helper function for `negate_expression`. To check for a removable
    /// negation, for expression `ex` call with `has_neg` initially set to
    /// false, i.e. `ex.has_removable_negation_inside(false)`.
    fn has_removable_negation_inside(&self, has_neg: bool) -> bool {
        match self {
            IntegerExpression::Atom(_)
            | IntegerExpression::Const(_)
            | IntegerExpression::Param(_) => has_neg,
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                if *op == IntegerOp::Sub {
                    lhs.has_removable_negation_inside(!has_neg)
                        || rhs.has_removable_negation_inside(!has_neg)
                } else {
                    lhs.has_removable_negation_inside(has_neg)
                        || rhs.has_removable_negation_inside(has_neg)
                }
            }
            IntegerExpression::Neg(ex) => ex.has_removable_negation_inside(!has_neg),
        }
    }
}

impl<T: Atomic> From<NonMinusIntegerExpr<T>> for IntegerExpression<T> {
    fn from(val: NonMinusIntegerExpr<T>) -> Self {
        match val {
            NonMinusIntegerExpr::Atom(a) => IntegerExpression::Atom(a),
            NonMinusIntegerExpr::Const(c) => IntegerExpression::Const(c),
            NonMinusIntegerExpr::NegConst(c) => {
                IntegerExpression::Neg(Box::new(IntegerExpression::Const(c)))
            }
            NonMinusIntegerExpr::Param(p) => IntegerExpression::Param(p),
            NonMinusIntegerExpr::BinaryExpr(lhs, op, rhs) => IntegerExpression::BinaryExpr(
                Box::new((*lhs).into()),
                op.into(),
                Box::new((*rhs).into()),
            ),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::expressions::{Location, Variable};

    #[test]
    fn test_push_neg_to_atomics1() {
        // -(x - 5)
        let expr = IntegerExpression::Neg(Box::new(IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            IntegerOp::Sub,
            Box::new(IntegerExpression::Const(5)),
        )));

        // -1 * x + 5
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::NegConst(1)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::Atom(Variable::new("x"))),
            )),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::Const(5)),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr = Into::<IntegerExpression<_>>::into(got_expr);
        let expected_expr = Into::<IntegerExpression<Variable>>::into(expected_expr);
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
    }

    #[test]
    fn test_push_neg_to_atomics2() {
        // -(1 * (3 - 5))
        let expr: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(1)),
                IntegerOp::Mul,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Sub,
                    Box::new(IntegerExpression::Const(5)),
                )),
            )));

        // 1 * 3 + 5
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(1)),
            NonMinusIntegerOp::Mul,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::NegConst(3)),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::Const(5)),
            )),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr = Into::<IntegerExpression<_>>::into(got_expr);
        let expected_expr = Into::<IntegerExpression<Variable>>::into(expected_expr);
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
        assert_eq!(got_expr.try_to_evaluate_to_const(), Some(2))
    }

    #[test]
    fn test_push_neg_to_atomics3() {
        // 1 * (3 - 5)
        let expr: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Const(1)),
            IntegerOp::Mul,
            Box::new(IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(3)),
                IntegerOp::Sub,
                Box::new(IntegerExpression::Const(5)),
            )),
        );

        // 1 * 3 + -5
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(1)),
            NonMinusIntegerOp::Mul,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(3)),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::NegConst(5)),
            )),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr = Into::<IntegerExpression<_>>::into(got_expr);
        let expected_expr = Into::<IntegerExpression<Variable>>::into(expected_expr);
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
        assert_eq!(got_expr.try_to_evaluate_to_const(), Some(-2))
    }

    #[test]
    fn test_push_neg_to_atomics4() {
        // 42 + -(-3 * 9)
        let expr: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Const(42)),
            IntegerOp::Add,
            Box::new(IntegerExpression::Neg(Box::new(
                IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Const(
                        3,
                    )))),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Const(9)),
                ),
            ))),
        );

        // 42 + 3 * 9
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(42)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(3)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::Const(9)),
            )),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr: IntegerExpression<_> = got_expr.into();
        let expected_expr: IntegerExpression<Variable> = expected_expr.into();
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
        assert_eq!(got_expr.try_to_evaluate_to_const(), Some(69))
    }

    #[test]
    fn test_push_neg_to_atomics5() {
        // - (42 + 9 * -3)
        let expr: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(42)),
                IntegerOp::Add,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(9)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Param(
                        Parameter::new("n"),
                    )))),
                )),
            )));

        // -42 + 9 * 3
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::NegConst(42)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(9)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::Param(Parameter::new("n"))),
            )),
        );

        let got_expr: NonMinusIntegerExpr<_> = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr: IntegerExpression<_> = got_expr.into();
        let expected_expr: IntegerExpression<Variable> = expected_expr.into();
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
        assert_eq!(got_expr.try_to_evaluate_to_const(), None)
    }

    #[test]
    fn test_push_neg_to_atomics6() {
        // - (42  + (9 / 3 * -9))
        let expr: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(42)),
                IntegerOp::Add,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(9)),
                    IntegerOp::Div,
                    Box::new(IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(3)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Const(
                            9,
                        )))),
                    )),
                )),
            )));

        // -42 + 9 / 3 * 9
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::NegConst(42)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(9)),
                NonMinusIntegerOp::Div,
                Box::new(NonMinusIntegerExpr::BinaryExpr(
                    Box::new(NonMinusIntegerExpr::Const(3)),
                    NonMinusIntegerOp::Mul,
                    Box::new(NonMinusIntegerExpr::Const(9)),
                )),
            )),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr: IntegerExpression<_> = got_expr.into();
        let expected_expr: IntegerExpression<Variable> = expected_expr.into();
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
        assert_eq!(got_expr.try_to_evaluate_to_const(), Some(-42))
    }

    #[test]
    fn test_push_neg_to_atomics7() {
        // -1 * - (3 - 5)
        let expr: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Const(
                1,
            )))),
            IntegerOp::Mul,
            Box::new(IntegerExpression::Neg(Box::new(
                IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Sub,
                    Box::new(IntegerExpression::Const(5)),
                ),
            ))),
        );

        // -1 * (3 + 5)
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::NegConst(1)),
            NonMinusIntegerOp::Mul,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::NegConst(3)),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::Const(5)),
            )),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);

        let got_expr: IntegerExpression<_> = got_expr.into();
        let expected_expr: IntegerExpression<Variable> = expected_expr.into();
        assert_eq!(
            got_expr.try_to_evaluate_to_const(),
            expected_expr.try_to_evaluate_to_const()
        );
        assert_eq!(got_expr.try_to_evaluate_to_const(), Some(-2))
    }

    #[test]
    fn test_push_neg_to_atomics8() {
        // - (42 + 9 * (-3 - 5)) )
        let expr: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(42)),
                IntegerOp::Add,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(9)),
                    IntegerOp::Mul,
                    Box::new(-IntegerExpression::Const(3) - IntegerExpression::Const(5)),
                )),
            )));

        // -42 + 9 * (3 + -5)
        let expected_expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::NegConst(42)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(9)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::BinaryExpr(
                    Box::new(NonMinusIntegerExpr::Const(3)),
                    NonMinusIntegerOp::Add,
                    Box::new(NonMinusIntegerExpr::Const(5)),
                )),
            )),
        );

        let got_expr = expr.remove_unary_neg_and_sub();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_into_neg_param() {
        // -n
        let expr: IntegerExpression<Location> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Param(Parameter::new("n"))));

        let expected: NonMinusIntegerExpr<Location> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::NegConst(1)),
            NonMinusIntegerOp::Mul,
            Box::new(NonMinusIntegerExpr::Param(Parameter::new("n"))),
        );

        assert_eq!(NonMinusIntegerExpr::from(expr), expected);

        let got: IntegerExpression<Location> = Into::<IntegerExpression<_>>::into(expected);
        let expected: IntegerExpression<Location> =
            -IntegerExpression::Const(1) * IntegerExpression::Param(Parameter::new("n"));
        assert_eq!(got, expected);

        // n
        let expr = IntegerExpression::Atom(Parameter::new("n"));

        let expected = NonMinusIntegerExpr::Atom(Parameter::new("n"));

        assert_eq!(NonMinusIntegerExpr::from(expr), expected);
    }

    #[test]
    fn test_display_non_minus_integer_expression() {
        // 1 / (n + -5)
        let expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(1)),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Atom(Parameter::new("n"))),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::NegConst(5)),
            )),
        );
        assert_eq!(expr.to_string(), "(1 / (n + -5))");

        // 1 + (-1 * n + 5)
        let expr: NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(1)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::BinaryExpr(
                    Box::new(NonMinusIntegerExpr::NegConst(1)),
                    NonMinusIntegerOp::Mul,
                    Box::new(NonMinusIntegerExpr::Param(Parameter::new("n"))),
                )),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::Const(5)),
            )),
        );
        assert_eq!(expr.to_string(), "(1 + ((-1 * n) + 5))");
    }

    #[test]
    #[should_panic]
    fn test_non_minus_op() {
        let _ = NonMinusIntegerOp::from(IntegerOp::Sub);
    }
}

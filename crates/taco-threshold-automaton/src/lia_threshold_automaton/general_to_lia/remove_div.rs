//! Module for removing divisions by replacing them with multiplications by
//! fractions.
//!
//! This module contains the logic to remove all division operators from an
//! integer expression. Most importantly, it contains the conversion from
//! `NoMinusIntegerExpr` to [`NoDivIntegerExpr`].
//!
//! Integer expressions without divisions (and subtraction) are represented by
//! the type [`NoDivIntegerExpr`]. This type is a subset of the
//! [`NonMinusIntegerExpr`] type, which is a subset of the
//! [`crate::expressions::IntegerExpression`] type.

use crate::expressions::{Atomic, Parameter, fraction::Fraction};
use std::fmt::{Debug, Display};

use super::{
    ConstraintRewriteError,
    remove_minus::{NonMinusIntegerExpr, NonMinusIntegerOp},
};

#[derive(Debug, PartialEq, Clone, Copy)]
/// Integer operator that only allows for addition and multiplication
pub enum NoDivIntegerOp {
    /// +
    Add,
    /// *
    Mul,
}

impl Display for NoDivIntegerOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NoDivIntegerOp::Add => write!(f, "+"),
            NoDivIntegerOp::Mul => write!(f, "*"),
        }
    }
}

impl From<NonMinusIntegerOp> for NoDivIntegerOp {
    /// Convert a [`NonMinusIntegerOp`] to a [`NoDivIntegerOp`]
    ///
    /// Panics if the [`NonMinusIntegerOp`] is a [`NonMinusIntegerOp::Div`]
    fn from(op: NonMinusIntegerOp) -> Self {
        match op {
            NonMinusIntegerOp::Add => NoDivIntegerOp::Add,
            NonMinusIntegerOp::Mul => NoDivIntegerOp::Mul,
            NonMinusIntegerOp::Div => panic!("Division operator not allowed"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
/// Integer expression without division operators
pub enum NoDivIntegerExpr<T: Atomic> {
    /// Atom of type T
    Atom(T),
    /// Constant fraction
    Frac(Fraction),
    /// Parameter
    Param(Parameter),
    /// Integer expression combining two integer expressions through an
    /// arithmetic operator
    BinaryExpr(
        Box<NoDivIntegerExpr<T>>,
        NoDivIntegerOp,
        Box<NoDivIntegerExpr<T>>,
    ),
}

impl<T> NonMinusIntegerExpr<T>
where
    T: Atomic,
{
    /// Remove all division operators from the expression
    ///
    /// This function recursively evaluates the expression and tries to simplify
    /// it by removing all division operators. If the formula is not linear
    /// arithmetic, an error is returned. This is the case if a parameter or
    /// atom appears in the denominator of a division.
    ///
    /// Note that we do not implement full symbolic math, therefore it could be
    /// the case that the expression is linear arithmetic but requires
    /// simplification (e.g. that violating atom also appears in the denominator
    /// and could be removed by a simplification step).
    pub fn remove_div(self) -> Result<NoDivIntegerExpr<T>, ConstraintRewriteError> {
        match self {
            NonMinusIntegerExpr::Atom(a) => Ok(NoDivIntegerExpr::Atom(a)),
            NonMinusIntegerExpr::Const(c) => Ok(NoDivIntegerExpr::Frac(c.into())),
            NonMinusIntegerExpr::NegConst(c) => {
                Ok(NoDivIntegerExpr::Frac(-Into::<Fraction>::into(c)))
            }
            NonMinusIntegerExpr::Param(parameter) => Ok(NoDivIntegerExpr::Param(parameter)),
            NonMinusIntegerExpr::BinaryExpr(numerator, NonMinusIntegerOp::Div, denominator) => {
                // try to parse the denominator into a fraction
                // This must be possible for a linear arithmetic formula,
                // otherwise we have an expression of the form 1/param or 1/var
                let denominator = denominator
                    .try_to_fraction()
                    .ok_or(ConstraintRewriteError::NotLinearArithmetic)?;

                // check if the numerator is also a constant and simplify
                if let Some(numerator) = numerator.try_to_fraction() {
                    return Ok(NoDivIntegerExpr::Frac(numerator / denominator));
                }

                // if the numerator is not a constant, we need to recursively
                // evaluate the expression and add the fraction as a factor
                Ok(NoDivIntegerExpr::BinaryExpr(
                    Box::new(NoDivIntegerExpr::Frac(Fraction::from(1) / denominator)),
                    NoDivIntegerOp::Mul,
                    Box::new(numerator.remove_div()?),
                ))
            }
            NonMinusIntegerExpr::BinaryExpr(lhs, op, rhs) => {
                let lhs = lhs.remove_div()?;
                let rhs = rhs.remove_div()?;
                Ok(NoDivIntegerExpr::BinaryExpr(
                    Box::new(lhs),
                    op.into(),
                    Box::new(rhs),
                ))
            }
        }
    }

    /// Attempt to parse the expression into a fraction by recursively
    /// evaluating the expression
    ///
    /// This function returns `None` if the expression contains any atoms or
    /// parameters. Otherwise, it returns a fraction equivalent to the original
    /// expression
    pub fn try_to_fraction(&self) -> Option<Fraction> {
        match self {
            NonMinusIntegerExpr::Atom(_) | NonMinusIntegerExpr::Param(_) => None,
            NonMinusIntegerExpr::Const(c) => Some(Fraction::new(*c, 1, false)),
            NonMinusIntegerExpr::NegConst(c) => Some(Fraction::new(*c, 1, true)),
            NonMinusIntegerExpr::BinaryExpr(lhs, op, rhs) => {
                let lhs = lhs.try_to_fraction()?;
                let rhs = rhs.try_to_fraction()?;

                match op {
                    NonMinusIntegerOp::Add => Some(lhs + rhs),
                    NonMinusIntegerOp::Mul => Some(lhs * rhs),
                    NonMinusIntegerOp::Div => Some(lhs / rhs),
                }
            }
        }
    }
}

impl<T: Atomic> TryFrom<NonMinusIntegerExpr<T>> for NoDivIntegerExpr<T> {
    type Error = ConstraintRewriteError;

    fn try_from(value: NonMinusIntegerExpr<T>) -> Result<Self, Self::Error> {
        value.remove_div()
    }
}

impl<T> Display for NoDivIntegerExpr<T>
where
    T: Atomic,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NoDivIntegerExpr::Atom(a) => write!(f, "{a}"),
            NoDivIntegerExpr::Frac(fraction) => write!(f, "{fraction}"),
            NoDivIntegerExpr::Param(parameter) => write!(f, "{parameter}"),
            NoDivIntegerExpr::BinaryExpr(lhs, op, rhs) => write!(f, "({lhs} {op} {rhs})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expressions::Variable;

    #[test]
    fn test_keep_no_div_add() {
        // 3 + -5
        let expr: NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(3)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::NegConst(5)),
        );

        // (3/1) + (5/1)
        let expected_expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(3, 1, false))),
            NoDivIntegerOp::Add,
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(5, 1, true))),
        );

        let got_expr = NoDivIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_keep_no_div_mul() {
        // 4 + (-7 * -2)
        let expr: NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(4)),
            NonMinusIntegerOp::Add,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::NegConst(7)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::NegConst(2)),
            )),
        );

        // (4/1) + (7/1 * 2/1)
        let expected_expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(4, 1, false))),
            NoDivIntegerOp::Add,
            Box::new(NoDivIntegerExpr::BinaryExpr(
                Box::new(NoDivIntegerExpr::Frac(Fraction::new(7, 1, true))),
                NoDivIntegerOp::Mul,
                Box::new(NoDivIntegerExpr::Frac(Fraction::new(2, 1, true))),
            )),
        );

        let got_expr = NoDivIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_simple_division() {
        // x / 2
        let expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Atom(Variable::new("x"))),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::Const(2)),
        );

        // 1/2 * x
        let expected_expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(1, 2, false))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
        );

        let got_expr = expr.remove_div().unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_division_both_const() {
        // (3 + 2) / -4
        let expr: NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(3)),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::Const(2)),
            )),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::NegConst(4)),
        );

        // (5/24)
        let expected_expr = NoDivIntegerExpr::Frac(Fraction::new(5, 4, true));

        let got_expr = expr.remove_div().unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_double_division() {
        // x / (1 / 2)
        let expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Atom(Variable::new("x"))),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(1)),
                NonMinusIntegerOp::Div,
                Box::new(NonMinusIntegerExpr::Const(2)),
            )),
        );

        // 2 * x
        let expected_expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(2, 1, false))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
        );

        let got_expr = expr.remove_div().unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_simple_from_var() {
        // x / (3 + 2)
        let expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Atom(Variable::new("x"))),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(3)),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::Const(2)),
            )),
        );

        // 1/5 * x
        let expected_expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(1, 5, false))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
        );

        let got_expr = NoDivIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn try_simple_from_param() {
        // n / (5 * 2)
        let expr: NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Param(Parameter::new("n"))),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Const(5)),
                NonMinusIntegerOp::Mul,
                Box::new(NonMinusIntegerExpr::Const(2)),
            )),
        );

        // 1/10 * n
        let expected_expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(1, 10, false))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Param(Parameter::new("n"))),
        );
        let got_expr = NoDivIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got_expr, expected_expr);
    }

    #[test]
    fn test_error_on_div_by_var() {
        // 1 / x
        let expr = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(1)),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::Atom(Variable::new("x"))),
        );
        let e = NoDivIntegerExpr::try_from(expr);
        assert!(e.is_err());
        assert!(matches!(
            e.unwrap_err(),
            ConstraintRewriteError::NotLinearArithmetic
        ));
    }

    #[test]
    fn test_error_on_div_by_param() {
        // 1 / (n + 5)
        let expr: NonMinusIntegerExpr<Variable> = NonMinusIntegerExpr::BinaryExpr(
            Box::new(NonMinusIntegerExpr::Const(1)),
            NonMinusIntegerOp::Div,
            Box::new(NonMinusIntegerExpr::BinaryExpr(
                Box::new(NonMinusIntegerExpr::Param(Parameter::new("n"))),
                NonMinusIntegerOp::Add,
                Box::new(NonMinusIntegerExpr::Const(5)),
            )),
        );

        let e = NoDivIntegerExpr::try_from(expr);
        assert!(e.is_err());
        assert!(matches!(
            e.unwrap_err(),
            ConstraintRewriteError::NotLinearArithmetic
        ));
    }

    #[test]
    fn test_display_no_div_integer_expr() {
        let expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Frac(Fraction::new(1, 2, false))),
        );
        assert_eq!(format!("{expr}"), "(x * 1/2)");

        let expr = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
            NoDivIntegerOp::Add,
            Box::new(NoDivIntegerExpr::Param(Parameter::new("p"))),
        );

        assert_eq!(format!("{expr}"), "(x + p)");
    }

    #[test]
    #[should_panic]
    fn test_no_div_op_div() {
        let _ = NoDivIntegerOp::from(NonMinusIntegerOp::Div);
    }
}

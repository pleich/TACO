//! This module contains the logic to split an integer expression into pairs of
//! factors and an atom / parameter or constant.
//!
//! The general outline of the conversion is described in more detail in
//! [`../general_to_lia.rs`](general_to_lia.rs).

use log::debug;
use std::fmt::{Debug, Display};

use crate::expressions::{Atomic, Parameter, fraction::Fraction};

use super::{
    ConstraintRewriteError,
    remove_div::{NoDivIntegerExpr, NoDivIntegerOp},
};

/// Pair of an atom and a factor
#[derive(Debug, Clone, PartialEq)]
pub enum AtomFactorPair<T: Display + Debug + Clone> {
    Atom(T, Fraction),
    Param(Parameter, Fraction),
    Const(Fraction),
}

#[derive(Debug, Clone, PartialEq)]
/// Type to represent a linear arithmetic expression
pub struct LinearIntegerExpr<T: Display + Debug + Clone> {
    /// Pairs part of a sum
    pairs: Vec<AtomFactorPair<T>>,
}

impl<T: Atomic> NoDivIntegerExpr<T> {
    /// Split the expression into pairs of factors and an atom / parameter or constant
    pub fn split_into_factor_pairs(self) -> Result<LinearIntegerExpr<T>, ConstraintRewriteError> {
        let pairs = self.collect_pairs()?;

        Ok(LinearIntegerExpr { pairs })
    }

    fn collect_pairs(self) -> Result<Vec<AtomFactorPair<T>>, ConstraintRewriteError> {
        match self {
            NoDivIntegerExpr::Atom(a) => Ok(vec![AtomFactorPair::Atom(a, 1.into())]),
            NoDivIntegerExpr::Frac(f) => Ok(vec![AtomFactorPair::Const(f)]),
            NoDivIntegerExpr::Param(p) => Ok(vec![AtomFactorPair::Param(p, 1.into())]),
            NoDivIntegerExpr::BinaryExpr(lhs, op, rhs) => match op {
                NoDivIntegerOp::Add => {
                    let mut lhs = lhs.collect_pairs()?;
                    let rhs = rhs.collect_pairs()?;

                    lhs.extend(rhs);
                    Ok(lhs)
                }
                NoDivIntegerOp::Mul => {
                    let lhs_f = lhs.clone().try_to_fraction();
                    let rhs_f = rhs.clone().try_to_fraction();

                    // both sides of the multiplication contain parameters or
                    // atoms, the expression is not linear arithmetic
                    if lhs_f.is_none() && rhs_f.is_none() {
                        debug!("Failed to split expression ({lhs} * {rhs}) into factor pairs");
                        return Err(ConstraintRewriteError::NotLinearArithmetic);
                    }

                    // if both sides are constants, we can simplify the expression
                    if let (Some(lhs_f), Some(rhs_f)) = (lhs_f, rhs_f) {
                        return Ok(vec![AtomFactorPair::Const(lhs_f * rhs_f)]);
                    }

                    // one is constant, the other contains parameters or atoms
                    let (const_, non_const_expr) = if let Some(lhs) = lhs_f {
                        (lhs, rhs.collect_pairs()?)
                    } else {
                        (rhs_f.unwrap(), lhs.collect_pairs()?)
                    };

                    // add constant factor to all of the pairs
                    Ok(non_const_expr
                        .into_iter()
                        .map(|atom| match atom {
                            AtomFactorPair::Atom(a, f) => AtomFactorPair::Atom(a, f * const_),
                            AtomFactorPair::Param(p, f) => AtomFactorPair::Param(p, f * const_),
                            AtomFactorPair::Const(f) => AtomFactorPair::Const(f * const_), // unreachable
                        })
                        .collect())
                }
            },
        }
    }

    /// Try to convert the expression to a fraction
    pub fn try_to_fraction(self) -> Option<Fraction> {
        match self {
            NoDivIntegerExpr::Atom(_) | NoDivIntegerExpr::Param(_) => None,
            NoDivIntegerExpr::Frac(f) => Some(f),
            NoDivIntegerExpr::BinaryExpr(lhs, op, rhs) => {
                let lhs = lhs.try_to_fraction()?;
                let rhs = rhs.try_to_fraction()?;

                match op {
                    NoDivIntegerOp::Add => Some(lhs + rhs),
                    NoDivIntegerOp::Mul => Some(lhs * rhs),
                }
            }
        }
    }
}

impl<T: Atomic> TryFrom<NoDivIntegerExpr<T>> for LinearIntegerExpr<T> {
    type Error = ConstraintRewriteError;

    fn try_from(value: NoDivIntegerExpr<T>) -> Result<Self, Self::Error> {
        value.split_into_factor_pairs()
    }
}

impl<T: Display + Debug + Clone> LinearIntegerExpr<T> {
    /// Get the constant factor of the expression
    ///
    /// For an expression of the form `a * x + b * y + p * z + c`, where `a, b`
    /// and `p` are coefficients and `x,y,z` are parameters and c a constant,
    /// this function returns `c`.
    pub fn get_const_factor(&self) -> Fraction {
        self.pairs
            .iter()
            .filter_map(|pair| match pair {
                AtomFactorPair::Const(f) => Some(*f),
                _ => None,
            })
            .fold(Fraction::from(0), |acc, f| acc + f)
    }

    /// Get all atom factor pairs of the expression
    ///
    /// For an expression of the form `a * x + b * y + p * z + c`, where `x` and `y` are atoms,
    /// `a` and `b` are their coefficients, `p` is a parameter, and `z` is its coefficient,
    /// this function returns the pairs `(x, a), (y, b)`.
    pub fn get_atom_factor_pairs(&self) -> impl Iterator<Item = (&T, &Fraction)> {
        self.pairs
            .iter()
            .filter(|pair| matches!(pair, AtomFactorPair::Atom(_, _)))
            .map(|pair| match pair {
                AtomFactorPair::Atom(a, f) => (a, f),
                _ => unreachable!(),
            })
    }

    /// Get all parameter factor pairs of the expression
    ///
    /// For an expression of the form `a * x + b * y + p * z + c`, where `x, y, z` are parameters
    /// and `a, b, p` are their coefficients, this function returns the pairs `(p, z)`, where
    /// `p` is the parameter and `z` is its coefficient.
    pub fn get_param_factor_pairs(&self) -> impl Iterator<Item = (&Parameter, &Fraction)> {
        self.pairs
            .iter()
            .filter(|pair| matches!(pair, AtomFactorPair::Param(_, _)))
            .map(|pair| match pair {
                AtomFactorPair::Param(p, f) => (p, f),
                _ => unreachable!(),
            })
    }
}

impl<T: Display + Debug + Clone> Display for AtomFactorPair<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomFactorPair::Atom(a, frac) => write!(f, "{a} * {frac}"),
            AtomFactorPair::Param(p, frac) => write!(f, "{p} * {frac}"),
            AtomFactorPair::Const(c) => write!(f, "{c}"),
        }
    }
}

impl<T: Display + Debug + Clone> Display for LinearIntegerExpr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut it = self.pairs.iter();
        if let Some(pair) = it.next() {
            write!(f, "{pair}")?;
        }

        it.try_for_each(|pair| write!(f, " + {pair}"))
    }
}

#[cfg(test)]
mod test {
    use crate::expressions::Variable;

    use super::*;

    #[test]
    fn test_simple_frac() {
        // 1
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::Frac(2.into());

        let expected: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![AtomFactorPair::Const(2.into())],
        };

        let got = LinearIntegerExpr::try_from(expr).unwrap();

        assert_eq!(got, expected);
    }

    #[test]
    fn simple_addition_no_mul() {
        // 1 + n
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(1.into())),
            NoDivIntegerOp::Add,
            Box::new(NoDivIntegerExpr::Param(Parameter::new("n"))),
        );

        let expected: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![
                AtomFactorPair::Const(1.into()),
                AtomFactorPair::Param(Parameter::new("n"), 1.into()),
            ],
        };

        let got = LinearIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn test_simple_mul_lhs_const() {
        // 1 * x
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(1.into())),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
        );

        let expected: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![AtomFactorPair::Atom(Variable::new("x"), 1.into())],
        };

        let got = LinearIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn test_simple_mul_rhs_const() {
        // x * 1
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Frac(1.into())),
        );

        let expected: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![AtomFactorPair::Atom(Variable::new("x"), 1.into())],
        };

        let got = LinearIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn test_simple_mul_const_param() {
        // 1 * n
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(1.into())),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Param(Parameter::new("n"))),
        );

        let expected: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![AtomFactorPair::Param(Parameter::new("n"), 1.into())],
        };

        let got = LinearIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn test_simple_mul_both_const() {
        // 1 * 5
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(1.into())),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Frac(5.into())),
        );

        let expected: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![AtomFactorPair::Const(5.into())],
        };

        let got = LinearIntegerExpr::try_from(expr).unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn test_simple_mul_both_non_const() {
        // x * n
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Atom(Variable::new("x"))),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Param(Parameter::new("n"))),
        );

        let got = LinearIntegerExpr::try_from(expr);
        assert!(got.is_err());
        assert!(matches!(
            got.unwrap_err(),
            ConstraintRewriteError::NotLinearArithmetic
        ));
    }

    #[test]
    fn test_try_to_fraction() {
        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::Frac(5.into());
        assert_eq!(expr.try_to_fraction(), Some(5.into()));

        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::Atom(Variable::new("x"));
        assert_eq!(expr.try_to_fraction(), None);

        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(5.into())),
            NoDivIntegerOp::Mul,
            Box::new(NoDivIntegerExpr::Frac(3.into())),
        );
        assert_eq!(expr.try_to_fraction(), Some(15.into()));

        let expr: NoDivIntegerExpr<Variable> = NoDivIntegerExpr::BinaryExpr(
            Box::new(NoDivIntegerExpr::Frac(2.into())),
            NoDivIntegerOp::Add,
            Box::new(NoDivIntegerExpr::Frac(5.into())),
        );
        assert_eq!(expr.try_to_fraction(), Some(7.into()))
    }

    #[test]
    fn test_get_atom_factor_pairs() {
        let expr: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![
                AtomFactorPair::Atom(Variable::new("x"), 5.into()),
                AtomFactorPair::Param(Parameter::new("p"), 3.into()),
                AtomFactorPair::Const(7.into()),
            ],
        };

        let pairs: Vec<(&Variable, &Fraction)> = expr.get_atom_factor_pairs().collect();
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0], (&Variable::new("x"), &5.into()));
    }

    #[test]
    fn test_get_param_factor_pairs() {
        let expr: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![
                AtomFactorPair::Atom(Variable::new("x"), 5.into()),
                AtomFactorPair::Param(Parameter::new("p"), 3.into()),
                AtomFactorPair::Const(7.into()),
            ],
        };

        let pairs: Vec<(&Parameter, &Fraction)> = expr.get_param_factor_pairs().collect();
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0], (&Parameter::new("p"), &3.into()));
    }

    #[test]
    fn test_get_const_factor() {
        let expr: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![
                AtomFactorPair::Atom(Variable::new("x"), 5.into()),
                AtomFactorPair::Param(Parameter::new("p"), 3.into()),
                AtomFactorPair::Const(7.into()),
                AtomFactorPair::Const(5.into()),
            ],
        };

        assert_eq!(expr.get_const_factor(), 12.into());
    }

    #[test]
    fn test_display_linear_integer_arithmetic_expr() {
        let expr: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![
                AtomFactorPair::Atom(Variable::new("x"), 5.into()),
                AtomFactorPair::Param(Parameter::new("p"), 3.into()),
                AtomFactorPair::Const(7.into()),
            ],
        };
        assert_eq!(expr.to_string(), "x * 5 + p * 3 + 7");

        let expr: LinearIntegerExpr<Variable> = LinearIntegerExpr {
            pairs: vec![AtomFactorPair::Const(7.into())],
        };
        assert_eq!(expr.to_string(), "7");
    }
}

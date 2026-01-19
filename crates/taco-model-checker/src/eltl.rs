//! ELTL (LTL without next) expressions for threshold automata
//!
//! This module provides the types defining ELTL expressions  without a next
//! operator for threshold automata. In the literature these formulas are also
//! called ELTL or fault-tolerant temporal logic.
//!
//! Use the [`ELTLSpecificationBuilder`] to create a new ELTL specification, which
//! is guaranteed to only contain variables, locations and parameters that are
//! declared in the threshold automaton associated with the builder.
//!
//! Note that these ELTL formulas do not match the formal definition outlined in
//! many papers. The reason for that is that benchmarks do not conform to the
//! formal specification. We recommend using the more restricted internal
//! specification types when writing a model checker.

use std::{
    collections::HashMap,
    fmt,
    ops::{BitAnd, BitOr, Not},
    vec,
};
use taco_display_utils::TAB_SIZE;
use taco_threshold_automaton::{
    ThresholdAutomaton,
    expressions::{
        Atomic, BooleanExpression, ComparisonOp, IntegerExpression, IsDeclared, Location,
        Parameter, Variable,
    },
};

pub mod remove_negations;

/// ELTL (LTL without next) expressions for threshold automata
///
/// This module provides the types defining ELTL expressions  without a next
/// operator for threshold automata. In the literature these formulas are also
/// called ELTL or fault-tolerant temporal logic.
///
/// # Example
///
/// ```
/// use taco_threshold_automaton::expressions::{IntegerExpression, ComparisonOp, Location};
/// use taco_model_checker::eltl::ELTLExpression;
///
/// // loc1 = 0 => □(loc_agree_1 = 0)
/// let _ = ELTLExpression::Implies(
///  Box::new(ELTLExpression::LocationExpr(
///     Box::new(IntegerExpression::Atom(Location::new("loc1"))),
///     ComparisonOp::Eq,
///     Box::new(IntegerExpression::Const(0)),
///  )),
///  Box::new(ELTLExpression::Globally(
///     Box::new(ELTLExpression::LocationExpr(
///         Box::new(IntegerExpression::Atom(Location::new("loc_agree_1"))),
///         ComparisonOp::Eq,
///         Box::new(IntegerExpression::Const(0)),
///     )),
///  )));
/// ```
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum ELTLExpression {
    /// Implication ⟹
    Implies(Box<ELTLExpression>, Box<ELTLExpression>),
    /// Globally □
    Globally(Box<ELTLExpression>),
    /// Eventually ◇
    Eventually(Box<ELTLExpression>),
    /// And ∧
    And(Box<ELTLExpression>, Box<ELTLExpression>),
    /// Or ∨
    Or(Box<ELTLExpression>, Box<ELTLExpression>),
    /// Not ¬
    Not(Box<ELTLExpression>),
    /// Boolean constraint over the number of processes in a location
    LocationExpr(
        Box<IntegerExpression<Location>>,
        ComparisonOp,
        Box<IntegerExpression<Location>>,
    ),
    /// Boolean constraint over the value of a variable
    VariableExpr(
        Box<IntegerExpression<Variable>>,
        ComparisonOp,
        Box<IntegerExpression<Variable>>,
    ),
    /// Expression over the value of parameters
    ParameterExpr(
        Box<IntegerExpression<Parameter>>,
        ComparisonOp,
        Box<IntegerExpression<Parameter>>,
    ),
    /// Always true
    True,
    /// Always false
    False,
}

impl ELTLExpression {
    /// Check if the expression contains a temporal operator
    ///
    /// Returns `true` if the expression contains a temporal operator,
    /// otherwise `false`
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::{IntegerExpression, ComparisonOp, Location};
    /// use taco_model_checker::eltl::ELTLExpression;
    ///
    /// let expression = ELTLExpression::LocationExpr(
    ///     Box::new(IntegerExpression::Atom(Location::new("loc1"))),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Atom(Location::new("loc2"))),
    /// );
    /// assert!(!expression.contains_temporal_operator());
    ///
    /// let expression = ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
    ///     Box::new(IntegerExpression::Atom(Location::new("loc1"))),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Atom(Location::new("loc2"))),
    /// )));
    /// assert!(expression.contains_temporal_operator());
    /// ```
    pub fn contains_temporal_operator(&self) -> bool {
        match self {
            ELTLExpression::Globally(_) | ELTLExpression::Eventually(_) => true,
            ELTLExpression::True
            | ELTLExpression::False
            | ELTLExpression::LocationExpr(_, _, _)
            | ELTLExpression::ParameterExpr(_, _, _)
            | ELTLExpression::VariableExpr(_, _, _) => false,
            ELTLExpression::Implies(lhs, rhs) => {
                lhs.contains_temporal_operator() || rhs.contains_temporal_operator()
            }
            ELTLExpression::And(lhs, rhs) | ELTLExpression::Or(lhs, rhs) => {
                lhs.contains_temporal_operator() || rhs.contains_temporal_operator()
            }
            ELTLExpression::Not(expr) => expr.contains_temporal_operator(),
        }
    }
}

impl Not for ELTLExpression {
    type Output = Self;

    fn not(self) -> Self::Output {
        ELTLExpression::Not(Box::new(self))
    }
}

impl BitAnd for ELTLExpression {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        ELTLExpression::And(Box::new(self), Box::new(rhs))
    }
}

impl BitOr for ELTLExpression {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        ELTLExpression::Or(Box::new(self), Box::new(rhs))
    }
}

impl fmt::Display for ELTLExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ELTLExpression::Implies(lhs, rhs) => write!(f, "({lhs}) -> ({rhs})"),
            ELTLExpression::Globally(expression) => write!(f, "[]({expression})"),
            ELTLExpression::Eventually(expression) => write!(f, "<>({expression})"),
            ELTLExpression::And(lhs, rhs) => write!(f, "({lhs}) && ({rhs})"),
            ELTLExpression::Or(lhs, rhs) => write!(f, "({lhs}) || ({rhs})"),
            ELTLExpression::Not(expression) => write!(f, "!({expression})"),
            ELTLExpression::LocationExpr(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            ELTLExpression::VariableExpr(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            ELTLExpression::ParameterExpr(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            ELTLExpression::True => write!(f, "true"),
            ELTLExpression::False => write!(f, "false"),
        }
    }
}

/// [`ELTLExpression`] with associated name
///
/// This type represents an ELTLExpression that has a name associated with it
pub type ELTLProperty = (String, ELTLExpression);

/// A collection of [`ELTLProperty`] that in conjunction describe correct
/// behavior
///
/// An [`ELTLSpecification`] is a collection of [`ELTLProperty`]s (i.e.,
/// collection of named [`ELTLExpression`]s) that describe the desired behavior
/// of a threshold automaton. If threshold automaton fulfills all of the
/// properties, it can be considered safe with respect to the specification
#[derive(Debug, Clone, PartialEq)]
pub struct ELTLSpecification {
    /// Expressions and their associated names
    expressions: Vec<ELTLProperty>,
}

impl ELTLSpecification {
    /// Get a slice of the contained [`ELTLProperty`]s
    pub fn expressions(&self) -> &[ELTLProperty] {
        &self.expressions
    }
}

impl IntoIterator for ELTLSpecification {
    type Item = ELTLProperty;
    type IntoIter = vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.expressions.into_iter()
    }
}

impl fmt::Display for ELTLSpecification {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "specifications({}) {{", self.expressions.len())?;
        let indent = " ".repeat(TAB_SIZE);

        for (name, expression) in &self.expressions {
            writeln!(f, "{indent}{name}: {expression};")?;
        }

        write!(f, "}}")
    }
}

/// Builder for building an [`ELTLSpecification`] over a threshold automaton
///
/// # Example
///
/// ```
/// use taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder;
/// use taco_threshold_automaton::expressions::{IntegerExpression, ComparisonOp, Location, Variable};
/// use taco_model_checker::eltl::{ELTLExpression, ELTLSpecificationBuilder};
///
/// let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
///     .with_variables(vec![
///         Variable::new("var1"),
///         Variable::new("var2"),
///         Variable::new("var3"),
///     ])
///     .unwrap()
///     .with_locations(vec![
///         Location::new("loc1"),
///         Location::new("loc2"),
///     ])
///     .unwrap()
///     .initialize()
///     .build();
///
/// let mut builder = ELTLSpecificationBuilder::new(&ta);
///
/// let expr1 = ELTLExpression::LocationExpr(
///     Box::new(IntegerExpression::Atom(Location::new("loc1"))),
///     ComparisonOp::Eq,
///     Box::new(IntegerExpression::Const(2)),
/// );
///
/// let expr2 = ELTLExpression::LocationExpr(
///     Box::new(IntegerExpression::Atom(Location::new("loc2"))),
///     ComparisonOp::Eq,
///     Box::new(IntegerExpression::Const(0)),
/// );
///
/// builder.add_expressions(vec![
///     ("spec1".to_string(), expr1),
///     ("spec2".to_string(), expr2),
/// ]).unwrap();
///
/// let spec = builder.build();
///
/// assert_eq!(spec.expressions().len(), 2);
/// assert!(spec.expressions().iter().any(|(name, _)| name == "spec1"));
/// assert!(spec.expressions().iter().any(|(name, _)| name == "spec2"));
/// ```
pub struct ELTLSpecificationBuilder<'a, T: ThresholdAutomaton> {
    /// Threshold automaton associated with the expressions
    ta: &'a T,
    /// Collection of tuples of expression names and the ELTL expression
    properties: Vec<ELTLProperty>,
}

impl<T: ThresholdAutomaton> ELTLSpecificationBuilder<'_, T> {
    /// Check if all identifiers in the expression are known
    ///
    /// Returns `()` if no unknown identifier is found, otherwise the name of
    /// the unknown identifier
    fn check_for_unknown_identifier<S>(
        &self,
        expr: &IntegerExpression<S>,
    ) -> Result<(), InternalELTLExpressionBuilderError>
    where
        S: Atomic,
        Self: IsDeclared<S>,
    {
        match expr {
            IntegerExpression::Atom(a) => {
                if self.is_declared(a) {
                    Ok(())
                } else {
                    Err(InternalELTLExpressionBuilderError::UnknownIdentifier(
                        a.to_string(),
                    ))
                }
            }
            IntegerExpression::Const(_) => Ok(()),
            IntegerExpression::Param(p) => {
                if self.ta.is_declared(p) {
                    Ok(())
                } else {
                    Err(InternalELTLExpressionBuilderError::UnknownIdentifier(
                        p.to_string(),
                    ))
                }
            }
            IntegerExpression::BinaryExpr(lhs, _op, rhs) => {
                self.check_for_unknown_identifier(lhs)?;
                self.check_for_unknown_identifier(rhs)
            }
            IntegerExpression::Neg(expr) => self.check_for_unknown_identifier(expr),
        }
    }

    /// Check whether an ELTL expression contains a parameter expression
    fn check_contains_parameter_expression(
        expr: &ELTLExpression,
    ) -> Result<(), InternalELTLExpressionBuilderError> {
        match expr {
            ELTLExpression::Implies(lhs, rhs)
            | ELTLExpression::And(lhs, rhs)
            | ELTLExpression::Or(lhs, rhs) => {
                Self::check_contains_parameter_expression(lhs)?;
                Self::check_contains_parameter_expression(rhs)
            }
            ELTLExpression::Globally(expr)
            | ELTLExpression::Eventually(expr)
            | ELTLExpression::Not(expr) => Self::check_contains_parameter_expression(expr),
            ELTLExpression::True
            | ELTLExpression::False
            | ELTLExpression::LocationExpr(_, _, _)
            | ELTLExpression::VariableExpr(_, _, _) => Ok(()),
            ELTLExpression::ParameterExpr(lhs, op, rhs) => Err(
                InternalELTLExpressionBuilderError::ParameterExprBehindTemporalOperator(
                    lhs.clone(),
                    *op,
                    rhs.clone(),
                ),
            ),
        }
    }

    /// Replaces parameter expressions that do not contain parameters
    fn replace_trivial_expressions(expr: ELTLExpression) -> ELTLExpression {
        match expr {
            ELTLExpression::Globally(expr) => {
                ELTLExpression::Globally(Box::new(Self::replace_trivial_expressions(*expr)))
            }
            ELTLExpression::Eventually(expr) => {
                ELTLExpression::Eventually(Box::new(Self::replace_trivial_expressions(*expr)))
            }
            ELTLExpression::Not(expr) => {
                ELTLExpression::Not(Box::new(Self::replace_trivial_expressions(*expr)))
            }
            ELTLExpression::Implies(lhs, rhs) => ELTLExpression::Implies(
                Box::new(Self::replace_trivial_expressions(*lhs)),
                Box::new(Self::replace_trivial_expressions(*rhs)),
            ),
            ELTLExpression::And(lhs, rhs) => ELTLExpression::And(
                Box::new(Self::replace_trivial_expressions(*lhs)),
                Box::new(Self::replace_trivial_expressions(*rhs)),
            ),
            ELTLExpression::Or(lhs, rhs) => ELTLExpression::Or(
                Box::new(Self::replace_trivial_expressions(*lhs)),
                Box::new(Self::replace_trivial_expressions(*rhs)),
            ),
            ELTLExpression::LocationExpr(lhs, op, rhs) => {
                ELTLExpression::LocationExpr(lhs, op, rhs)
            }
            ELTLExpression::VariableExpr(lhs, op, rhs) => {
                ELTLExpression::VariableExpr(lhs, op, rhs)
            }
            ELTLExpression::ParameterExpr(lhs, op, rhs) => {
                if let Ok(eval) =
                    BooleanExpression::ComparisonExpression(lhs.clone(), op, rhs.clone())
                        .check_satisfied(&HashMap::new(), &HashMap::new())
                {
                    if eval {
                        return ELTLExpression::True;
                    }
                    return ELTLExpression::False;
                }
                ELTLExpression::ParameterExpr(lhs, op, rhs)
            }
            ELTLExpression::True => ELTLExpression::True,
            ELTLExpression::False => ELTLExpression::False,
        }
    }

    /// Check if all atoms in the expression are known in the threshold
    /// automaton associated with the builder and that all location expressions
    /// are valid
    fn validate_property(
        &self,
        expr: &ELTLExpression,
    ) -> Result<(), InternalELTLExpressionBuilderError> {
        match expr {
            ELTLExpression::Implies(lhs, rhs) => {
                self.validate_property(lhs)?;
                self.validate_property(rhs)
            }
            ELTLExpression::Globally(expression) | ELTLExpression::Eventually(expression) => {
                Self::check_contains_parameter_expression(expr)?;
                self.validate_property(expression)
            }
            ELTLExpression::And(lhs, rhs) => {
                self.validate_property(lhs)?;
                self.validate_property(rhs)
            }
            ELTLExpression::Or(lhs, rhs) => {
                self.validate_property(lhs)?;
                self.validate_property(rhs)
            }
            ELTLExpression::Not(expression) => self.validate_property(expression),
            ELTLExpression::LocationExpr(lhs, _, rhs) => {
                self.check_for_unknown_identifier(lhs)?;
                self.check_for_unknown_identifier(rhs)
            }
            ELTLExpression::VariableExpr(lhs, _, rhs) => {
                self.check_for_unknown_identifier(lhs)?;
                self.check_for_unknown_identifier(rhs)
            }
            ELTLExpression::ParameterExpr(lhs, _, rhs) => {
                self.check_for_unknown_identifier(lhs)?;
                self.check_for_unknown_identifier(rhs)
            }
            ELTLExpression::True | ELTLExpression::False => Ok(()),
        }
    }

    /// Add a new ELTL expression to the specification
    ///
    /// This function checks if all atoms in the expression are known in the
    /// threshold automaton associated with the builder. If an unknown atom is
    /// found, an error is returned. Otherwise the expression is added to the
    /// specification.
    ///
    /// This function also returns an error if the name of the expression is
    /// already used in the specification.
    pub fn add_expression(
        &mut self,
        name: String,
        expr: ELTLExpression,
    ) -> Result<(), ELTLExpressionBuilderError> {
        // check whether a property with the same name has already been added
        if self.properties.iter().any(|(n, _)| *n == name) {
            return Err(ELTLExpressionBuilderError::DuplicateName {
                property_name: name,
            });
        }

        // remove trivial parameter constraints
        let expr = Self::replace_trivial_expressions(expr);

        // validate the new property
        self.validate_property(&expr)
            .map_err(|internal_err| internal_err.into_builder_error(name.clone(), expr.clone()))?;

        self.properties.push((name, expr));
        Ok(())
    }

    /// Add multiple ELTL expressions to the specification
    ///
    /// This function checks if all atoms in the expression are known in the
    /// threshold automaton associated with the builder. If an unknown atom is
    /// found, an error is returned. Otherwise the expression is added to the
    /// specification.
    ///
    /// This function also returns an error if the name of the expression is
    /// already used in the specification.
    pub fn add_expressions(
        &mut self,
        expressions: impl IntoIterator<Item = ELTLProperty>,
    ) -> Result<(), ELTLExpressionBuilderError> {
        for (name, expression) in expressions {
            self.add_expression(name, expression)?;
        }
        Ok(())
    }

    /// Build the ELTL specification
    ///
    /// Returns the ELTL specification containing all added expressions
    pub fn build(self) -> ELTLSpecification {
        ELTLSpecification {
            expressions: self.properties,
        }
    }
}

impl<'a, T: ThresholdAutomaton> ELTLSpecificationBuilder<'a, T> {
    /// Create a new empty ELTL specification builder
    pub fn new(ta: &'a T) -> Self {
        ELTLSpecificationBuilder {
            ta,
            properties: Vec::new(),
        }
    }
}

impl<T: ThresholdAutomaton> IsDeclared<Variable> for ELTLSpecificationBuilder<'_, T> {
    fn is_declared(&self, obj: &Variable) -> bool {
        self.ta.is_declared(obj)
    }
}

impl<T: ThresholdAutomaton> IsDeclared<Location> for ELTLSpecificationBuilder<'_, T> {
    fn is_declared(&self, obj: &Location) -> bool {
        self.ta.is_declared(obj)
    }
}

impl<T: ThresholdAutomaton> IsDeclared<Parameter> for ELTLSpecificationBuilder<'_, T> {
    fn is_declared(&self, obj: &Parameter) -> bool {
        self.ta.is_declared(obj)
    }
}

/// Errors that can occur when building ELTL expressions over a threshold automaton
#[derive(Debug, Clone, PartialEq)]
pub enum ELTLExpressionBuilderError {
    /// Found an unknown atomic identifier
    UnknownIdentifier {
        /// Name of the ELTL expression
        property_name: String,
        /// Expression containing the unknown identifier
        expr: Box<ELTLExpression>,
        /// Unknown identifier
        ident: String,
    },
    /// Tried to add a specification with the same name twice to the specification
    DuplicateName {
        /// Name of the expression
        property_name: String,
    },
    /// Found an expression over parameters behind a temporal operator, which syntax is not defined
    ParameterConstraintBehindTemporalOperator {
        /// lhs of the constraint
        lhs: Box<IntegerExpression<Parameter>>,
        /// Comparison operator of the constraint
        op: ComparisonOp,
        /// rhs of the constraint
        rhs: Box<IntegerExpression<Parameter>>,
        /// Name of the expression
        property_name: String,
    },
}

/// Internal error type without the higher level property name
enum InternalELTLExpressionBuilderError {
    UnknownIdentifier(String),
    ParameterExprBehindTemporalOperator(
        Box<IntegerExpression<Parameter>>,
        ComparisonOp,
        Box<IntegerExpression<Parameter>>,
    ),
}

impl InternalELTLExpressionBuilderError {
    fn into_builder_error(
        self,
        property_name: String,
        expr: ELTLExpression,
    ) -> ELTLExpressionBuilderError {
        match self {
            InternalELTLExpressionBuilderError::UnknownIdentifier(ident) => {
                ELTLExpressionBuilderError::UnknownIdentifier {
                    property_name,
                    expr: Box::new(expr),
                    ident,
                }
            }
            InternalELTLExpressionBuilderError::ParameterExprBehindTemporalOperator(
                lhs,
                op,
                rhs,
            ) => ELTLExpressionBuilderError::ParameterConstraintBehindTemporalOperator {
                lhs,
                op,
                rhs,
                property_name,
            },
        }
    }
}

impl std::error::Error for ELTLExpressionBuilderError {}

impl fmt::Display for ELTLExpressionBuilderError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ELTLExpressionBuilderError::UnknownIdentifier {
                property_name: name,
                expr: _,
                ident,
            } => {
                write!(
                    f,
                    "Unknown identifier in specification '{name}': Identifier '{ident}' not known as parameter, location or variable"
                )
            }
            ELTLExpressionBuilderError::DuplicateName {
                property_name: name,
            } => {
                write!(
                    f,
                    "Duplicate name in specification: The name '{name}' is defined twice in the specification"
                )
            }
            ELTLExpressionBuilderError::ParameterConstraintBehindTemporalOperator {
                lhs,
                op,
                rhs,
                property_name,
            } => write!(
                f,
                "Constraint over parameters values found behind temporal operator in specification '{property_name}'. The constraint '{lhs} {op} {rhs}' only constrains the value of parameters, which do not update over time. Still the constraint appears behind a temporal operator. This is likely a mistake"
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use crate::eltl::ELTLExpressionBuilderError;

    use super::{ELTLExpression, ELTLSpecificationBuilder};
    use taco_threshold_automaton::expressions::{
        ComparisonOp, IntegerExpression, IntegerOp, Location, Parameter, Variable,
    };

    use taco_threshold_automaton::general_threshold_automaton::builder::{
        GeneralThresholdAutomatonBuilder, RuleBuilder,
    };
    use taco_threshold_automaton::general_threshold_automaton::{
        Action, GeneralThresholdAutomaton,
    };
    use taco_threshold_automaton::{BooleanVarConstraint, LocationConstraint, ParameterConstraint};

    lazy_static::lazy_static! {
        static ref TEST_TA: GeneralThresholdAutomaton = {
            GeneralThresholdAutomatonBuilder::new("test_ta1")
            .with_parameters(vec![
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ])
            .unwrap()
            .with_variables(vec![
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .with_locations(vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .initialize()
            .with_initial_variable_constraints(vec![BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )])
            .unwrap()
            .with_initial_location_constraints(vec![
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) & LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_resilience_conditions(vec![ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(3)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Atom(Parameter::new("f"))),
                )),
            )])
            .unwrap()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2"))
                    .with_actions(vec![Action::new(
                        Variable::new("var1"),
                        IntegerExpression::Atom(Variable::new("var1")),
                    )
                    .unwrap()])
                    .build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n")) - IntegerExpression::Const(2)),
                        ),
                    )
                    .with_actions(vec![
                        Action::new(Variable::new("var3"), IntegerExpression::Const(0)).unwrap(),
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::BinaryExpr(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                IntegerOp::Add,
                                Box::new(IntegerExpression::Const(1)),
                            ),
                        )
                        .unwrap(),
                    ])
                    .build(),
            ])
            .unwrap()
            .build()
        };
    }

    #[test]
    fn test_contains_temporal_operator() {
        let expression = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        );
        assert!(!expression.contains_temporal_operator());

        let expression = ELTLExpression::Implies(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc4"))),
            )),
        );
        assert!(!expression.contains_temporal_operator());

        let expression = ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        )));
        assert!(expression.contains_temporal_operator());

        let expression = ELTLExpression::Eventually(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        )));
        assert!(expression.contains_temporal_operator());

        let expression = ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            )),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
            )),
        );
        assert!(!expression.contains_temporal_operator());

        let expression = ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            )),
            Box::new(ELTLExpression::Not(Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc4"))),
            )))),
        );
        assert!(!expression.contains_temporal_operator());
    }

    #[test]
    fn test_ltl_expression_display() {
        let expression = ELTLExpression::True;
        assert_eq!(format!("{expression}"), "true");

        let expression = ELTLExpression::False;
        assert_eq!(format!("{expression}"), "false");

        let expression = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        );
        assert_eq!(format!("{expression}"), "loc1 == loc2");

        let expression = ELTLExpression::Implies(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc4"))),
            )),
        );
        assert_eq!(format!("{expression}"), "(loc1 == loc2) -> (loc3 == loc4)");

        let expression = ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        )));
        assert_eq!(format!("{expression}"), "[](loc1 == loc2)");

        let expression = ELTLExpression::Eventually(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        )));
        assert_eq!(format!("{expression}"), "<>(loc1 == loc2)");

        let expression = ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc4"))),
            )),
        );
        assert_eq!(format!("{expression}"), "(loc1 == loc2) && (loc3 == loc4)");

        let expression = ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Atom(Location::new("loc4"))),
            )),
        );
        assert_eq!(format!("{expression}"), "(loc1 == loc2) || (loc3 == loc4)");

        let expression = ELTLExpression::Not(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
        )));
        assert_eq!(format!("{expression}"), "!(loc1 == loc2)");
    }

    #[test]
    fn test_display_ltl_specification() {
        use super::{ELTLExpression, ELTLSpecification};
        use taco_threshold_automaton::expressions::{ComparisonOp, IntegerExpression, Location};

        let spec = ELTLSpecification {
            expressions: vec![
                (
                    "spec1".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ),
                ),
                (
                    "spec2".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Location::new("loc4"))),
                    ),
                ),
                (
                    "spec3".to_string(),
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ),
                ),
            ],
        };

        assert_eq!(
            format!("{spec}"),
            "specifications(3) {\n    spec1: loc1 == loc2;\n    spec2: loc3 == loc4;\n    spec3: var1 == n;\n}"
        );
    }

    #[test]
    fn test_operator_impl() {
        let ltl = ELTLExpression::True & ELTLExpression::False;
        let expected = ELTLExpression::And(
            Box::new(ELTLExpression::True),
            Box::new(ELTLExpression::False),
        );

        assert_eq!(ltl, expected);

        let ltl = ELTLExpression::True | ELTLExpression::False;
        let expected = ELTLExpression::Or(
            Box::new(ELTLExpression::True),
            Box::new(ELTLExpression::False),
        );

        assert_eq!(ltl, expected);
    }

    #[test]
    fn test_getter_ltl_specification() {
        use super::{ELTLExpression, ELTLSpecification};
        use taco_threshold_automaton::expressions::{ComparisonOp, IntegerExpression, Location};

        let spec = ELTLSpecification {
            expressions: vec![
                (
                    "spec1".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ),
                ),
                (
                    "spec2".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Location::new("loc4"))),
                    ),
                ),
            ],
        };

        assert_eq!(spec.expressions().len(), 2);
        assert_eq!(
            spec.expressions(),
            &[
                (
                    "spec1".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ),
                ),
                (
                    "spec2".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Atom(Location::new("loc4"))),
                    ),
                ),
            ]
        );
    }

    #[test]
    fn test_ltl_builder_add_expressions() {
        let ta = TEST_TA.clone();

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr1 = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(2)),
        );

        let expr2 = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc3"))),
            ComparisonOp::Eq,
            Box::new(-IntegerExpression::Const(3)),
        );

        let expr3 = ELTLExpression::True;

        builder
            .add_expressions(vec![
                ("spec1".to_string(), expr1),
                ("spec2".to_string(), expr2),
                ("spec3".to_string(), expr3),
            ])
            .unwrap();

        let spec = builder.build();
        assert_eq!(spec.expressions().len(), 3);
        assert_eq!(
            spec.expressions(),
            &[
                (
                    "spec1".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(2)),
                    ),
                ),
                (
                    "spec2".to_string(),
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                        ComparisonOp::Eq,
                        Box::new(-IntegerExpression::Const(3)),
                    ),
                ),
                ("spec3".to_string(), ELTLExpression::True),
            ]
        );
    }

    #[test]
    fn test_ltl_expr_builder_removes_trivial_param_expr() {
        let ta = TEST_TA.clone();

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr = ELTLExpression::ParameterExpr(
            Box::new(IntegerExpression::Const(2)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(2)),
        );

        builder
            .add_expressions(vec![("spec1".to_string(), expr)])
            .unwrap();

        let spec = builder.build();

        assert_eq!(spec.expressions().len(), 1);
        assert_eq!(
            spec.expressions(),
            &[("spec1".to_string(), ELTLExpression::True),]
        );

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr1 = ELTLExpression::Globally(Box::new(ELTLExpression::ParameterExpr(
            Box::new(IntegerExpression::Const(2)),
            ComparisonOp::Neq,
            Box::new(IntegerExpression::Const(2)),
        )));

        builder
            .add_expressions(vec![("spec1".to_string(), expr1)])
            .unwrap();

        let spec = builder.build();

        assert_eq!(spec.expressions().len(), 1);
        assert_eq!(
            spec.expressions(),
            &[(
                "spec1".to_string(),
                ELTLExpression::Globally(Box::new(ELTLExpression::False))
            ),]
        );
    }

    #[test]
    fn test_error_on_duplicate_spec_name() {
        let ta = TEST_TA.clone();

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr = ELTLExpression::ParameterExpr(
            Box::new(IntegerExpression::Const(2)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(3)),
        );

        builder
            .add_expressions(vec![("spec1".to_string(), expr)])
            .unwrap();

        let expr = ELTLExpression::True;

        let err = builder.add_expressions(vec![("spec1".to_string(), expr)]);

        assert!(err.is_err());
        let err = err.unwrap_err();

        let expected_err = ELTLExpressionBuilderError::DuplicateName {
            property_name: "spec1".into(),
        };

        assert_eq!(err, expected_err);

        assert!(err.to_string().contains("spec1"));
        assert!(err.to_string().contains("Duplicate"));
    }

    #[test]
    fn test_ltl_expr_builder_err_for_param_behind_temporal() {
        let ta = TEST_TA.clone();

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr = ELTLExpression::Eventually(Box::new(ELTLExpression::Implies(
            Box::new(ELTLExpression::True),
            Box::new(ELTLExpression::ParameterExpr(
                Box::new(IntegerExpression::Const(2)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
            )),
        )));

        let err = builder.add_expressions(vec![("spec1".to_string(), expr)]);

        assert!(err.is_err());
        let err = err.unwrap_err();

        let expected_err = ELTLExpressionBuilderError::ParameterConstraintBehindTemporalOperator {
            lhs: Box::new(IntegerExpression::Const(2)),
            op: ComparisonOp::Eq,
            rhs: Box::new(IntegerExpression::Param(Parameter::new("n"))),
            property_name: "spec1".into(),
        };

        assert_eq!(err, expected_err);

        assert!(err.to_string().contains("temporal operator"));
        assert!(err.to_string().contains("spec1"));
        assert!(err.to_string().contains("parameter"));
    }

    #[test]
    fn test_ltl_builder_test_add_expression_err_unknown_param() {
        let ta = TEST_TA.clone();

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr1 = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(2)),
        );

        let expr2 = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc3"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Param(Parameter::new("x"))),
        );

        let result = builder.add_expressions(vec![
            ("spec1".to_string(), expr1),
            ("spec2".to_string(), expr2),
        ]);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("Unknown"));
        assert!(err.to_string().contains(&Parameter::new("x").to_string()));

        let spec = builder.build();
        assert_eq!(spec.expressions().len(), 1);
    }

    #[test]
    fn test_ltl_builder_test_add_expression_err_unknown_loc() {
        let ta = TEST_TA.clone();

        let mut builder = ELTLSpecificationBuilder::new(&ta);

        let expr1 = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(2)),
        );

        let expr2 = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("loc3"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(Location::new("loc4"))),
        );

        let result = builder.add_expressions(vec![
            ("spec1".to_string(), expr1),
            ("spec2".to_string(), expr2),
        ]);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("Unknown"));
        assert!(err.to_string().contains(&Location::new("loc4").to_string()));

        let spec = builder.build();
        assert_eq!(spec.expressions().len(), 1);
    }
}

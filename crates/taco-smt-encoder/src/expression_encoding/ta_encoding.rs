//! Helper functions to encode expression of a threshold automaton into SMT
//! constraints

use taco_threshold_automaton::{
    ThresholdAutomaton, VariableConstraint,
    expressions::{Location, Parameter, Variable},
};

use crate::{
    SMTExpr, SMTSolver,
    expression_encoding::{EncodeToSMT, SMTVariableContext},
};

/// Encode the resilience conditions of a threshold automaton into an SMT
/// expression and return it
pub fn encode_resilience_condition<TA, C>(ta: &TA, solver: &SMTSolver, ctx: &C) -> SMTExpr
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter>,
{
    if ta.resilience_conditions().count() == 0 {
        return solver.true_();
    }

    let rc_it = ta
        .resilience_conditions()
        .map(|rc| {
            rc.encode_to_smt_with_ctx(solver, ctx)
                .expect("Failed to encode resilience condition")
        })
        .chain([solver.true_()]);
    solver.and_many(rc_it)
}

/// Encodes the initial variable and location constraints of the threshold
/// automaton in to an SMT expression
///
/// This function encodes the initial location and variable constraints of
/// the threshold automaton in to an SMT expression. To do so, it needs the
/// initial configuration of the threshold automaton, which is used as an
/// SMT variable context.
pub fn encode_initial_constraints<TA, C>(ta: &TA, solver: &SMTSolver, ctx: &C) -> SMTExpr
where
    TA: ThresholdAutomaton,
    C: SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>,
{
    if ta.initial_location_constraints().count() == 0
        && ta.initial_variable_constraints().count() == 0
    {
        return solver.true_();
    }

    let loc_init = ta.initial_location_constraints().map(|loc| {
        loc.encode_to_smt_with_ctx(solver, ctx)
            .expect("Failed to encode initial location condition")
    });

    let var_init = ta.initial_variable_constraints().map(|var| {
        var.as_boolean_expr()
            .encode_to_smt_with_ctx(solver, ctx)
            .expect("Failed to encode initial variable condition")
    });

    solver.and_many(loc_init.chain(var_init))
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, rc::Rc};

    use taco_threshold_automaton::{
        ThresholdAutomaton,
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder,
    };

    use crate::{
        SMTSolverBuilder,
        expression_encoding::{
            DeclaresVariable, EncodeToSMT,
            config_ctx::ConfigCtx,
            ta_encoding::{encode_initial_constraints, encode_resilience_condition},
        },
    };

    #[test]
    fn test_encode_rc_constraints() {
        let mut solver = SMTSolverBuilder::default().new_solver();

        let test_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_parameters([
                Parameter::new("n"),
                Parameter::new("t"),
                Parameter::new("f"),
            ])
            .unwrap()
            .initialize()
            .with_resilience_conditions([BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(
                    IntegerExpression::Const(3) * IntegerExpression::Atom(Parameter::new("t")),
                ),
            )])
            .unwrap()
            .build();

        let ctx: HashMap<Parameter, easy_smt::SExpr> = test_ta
            .parameters()
            .map(|p| {
                let param = p
                    .declare_variable(&mut solver, 0)
                    .expect("Failed to declare parameter");

                solver
                    .assert(solver.gte(param, solver.numeral(0)))
                    .expect("Failed to assert parameter >= 0");

                (p.clone(), param)
            })
            .collect::<HashMap<_, _>>();

        let got_expr = encode_resilience_condition(&test_ta, &solver, &ctx);

        let expected_expr = solver.and(
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(
                    IntegerExpression::Const(3) * IntegerExpression::Atom(Parameter::new("t")),
                ),
            )
            .encode_to_smt_with_ctx(&solver, &ctx)
            .unwrap(),
            solver.true_(),
        );

        assert_eq!(
            got_expr,
            expected_expr,
            "Got:{}\nExpected:{}",
            solver.display(got_expr),
            solver.display(expected_expr)
        )
    }

    #[test]
    fn test_initial_constraints() {
        let mut solver = SMTSolverBuilder::default().new_solver();

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
            .with_initial_location_constraints([
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .with_initial_variable_constraints([BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(0)),
            )])
            .unwrap()
            .build();

        let ctx = ConfigCtx::new(&mut solver, &test_ta, Rc::new(HashMap::new()), 0);

        let got_expr = encode_initial_constraints(&test_ta, &solver, &ctx);

        let expected_expr = solver.and_many([
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(0)),
            )
            .encode_to_smt_with_ctx(&solver, &ctx)
            .unwrap(),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )
            .encode_to_smt_with_ctx(&solver, &ctx)
            .unwrap(),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )
            .encode_to_smt_with_ctx(&solver, &ctx)
            .unwrap(),
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(0)),
            )
            .encode_to_smt_with_ctx(&solver, &ctx)
            .unwrap(),
        ]);

        assert_eq!(got_expr, expected_expr)
    }
}

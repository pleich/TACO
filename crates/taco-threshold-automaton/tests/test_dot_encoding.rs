//! Integration tests for output in the dot format.
//!
//! These tests require the `dot` feature to be enabled and graphviz to be
//! installed. If graphviz is not installed, the tests will be skipped.

#[cfg(all(test, feature = "dot"))]
mod graphviz_tests {
    use std::{
        borrow::BorrowMut,
        process::{Command, Stdio},
    };

    use taco_threshold_automaton::{
        BooleanVarConstraint, LocationConstraint, ParameterConstraint,
        dot::{DOTDiff, ToDOT},
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{
            Action,
            builder::{GeneralThresholdAutomatonBuilder, RuleBuilder},
        },
        lia_threshold_automaton::LIAThresholdAutomaton,
    };

    #[test]
    fn test_ta_dot_vis() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
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
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                    )
                    .with_action(Action::new_reset(Variable::new("var3")))
                    .with_action(
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1"))
                                + IntegerExpression::Const(1),
                        )
                        .unwrap(),
                    )
                    .build(),
            ])
            .unwrap()
            .with_initial_location_constraint(
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            )
            .unwrap()
            .with_initial_variable_constraint(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ))
            .unwrap()
            .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(
                    IntegerExpression::Const(3) * IntegerExpression::Atom(Parameter::new("f")),
                ),
            ))
            .unwrap()
            .build();

        test_dot_format_parses(ta.get_dot_graph());
    }

    #[test]
    fn test_lia_encoding() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
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
            .with_rules(vec![
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ),
                    )
                    .with_action(Action::new_reset(Variable::new("var3")))
                    .with_action(
                        Action::new(
                            Variable::new("var1"),
                            IntegerExpression::Atom(Variable::new("var1"))
                                + IntegerExpression::Const(1),
                        )
                        .unwrap(),
                    )
                    .build(),
            ])
            .unwrap()
            .with_initial_location_constraint(
                LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(
                        IntegerExpression::Param(Parameter::new("n"))
                            - IntegerExpression::Param(Parameter::new("f")),
                    ),
                ) | LocationConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            )
            .unwrap()
            .with_initial_variable_constraint(BooleanVarConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ))
            .unwrap()
            .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Gt,
                Box::new(
                    IntegerExpression::Const(3) * IntegerExpression::Atom(Parameter::new("f")),
                ),
            ))
            .unwrap()
            .build();

        let lta = LIAThresholdAutomaton::try_from(ta).unwrap().get_dot_graph();

        test_dot_format_parses(lta);
    }

    #[test]
    fn test_dot_diff() {
        let loc1 = Location::new("loc1");
        let loc2 = Location::new("loc2");
        let loc3 = Location::new("loc3");
        let loc4 = Location::new("loc4");
        let loc5 = Location::new("loc5");

        let var1 = Variable::new("var1");
        let var2 = Variable::new("var2");

        let r0 = RuleBuilder::new(0, loc1.clone(), loc1.clone()).build();
        let r1 = RuleBuilder::new(1, loc1.clone(), loc2.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r2 = RuleBuilder::new(2, loc2.clone(), loc3.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();
        let r3 = RuleBuilder::new(3, loc4.clone(), loc5.clone())
            .with_guard(BooleanVarConstraint::True)
            .build();

        let ta = GeneralThresholdAutomatonBuilder::new("ta")
            .with_parameters(vec![])
            .unwrap()
            .with_variables(vec![var1.clone(), var2.clone()])
            .unwrap()
            .with_locations(vec![
                loc1.clone(),
                loc2.clone(),
                loc3.clone(),
                loc4.clone(),
                loc5.clone(),
            ])
            .unwrap()
            .initialize()
            .with_rules(vec![r0.clone(), r1.clone(), r2.clone(), r3.clone()])
            .unwrap()
            .with_initial_location_constraints(vec![
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc4.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        let ta_processed = GeneralThresholdAutomatonBuilder::new("ta")
            .with_parameters(vec![])
            .unwrap()
            .with_variables(vec![var1.clone(), var2.clone()])
            .unwrap()
            .with_locations(vec![loc1.clone(), loc2.clone(), loc3.clone()])
            .unwrap()
            .initialize()
            .with_rules(vec![r0, r1, r2])
            .unwrap()
            .with_initial_location_constraints(vec![
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc2.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
                BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(loc3.clone())),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ])
            .unwrap()
            .build();

        let dot_ta = ta.get_dot_diff(&ta_processed);

        test_dot_format_parses(dot_ta);
    }

    fn test_dot_format_parses(dot: String) {
        if Command::new("dot")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .is_err()
        {
            println!("Graphviz is not installed on the system. Skipping test");
            return;
        }

        let mut echo_cmd = Command::new("echo")
            .arg(dot)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();

        let _ = echo_cmd.borrow_mut().wait();

        let dot_cmd = Command::new("dot")
            .stdin(echo_cmd.stdout.unwrap())
            .arg("-Tpng")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute graphviz: {err}"));

        assert!(
            dot_cmd.status.success(),
            "Failed to execute dot: stdout: {}; stderr: {}",
            String::from_utf8(dot_cmd.stdout).unwrap(),
            String::from_utf8(dot_cmd.stderr).unwrap()
        );
    }
}

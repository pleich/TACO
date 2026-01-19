//! This module defines the  `ConfigContext` type which declares all SMT
//! variables required to represent a configuration inside an SMT encoding

use core::fmt;
use std::{collections::HashMap, rc::Rc};

use taco_display_utils::join_iterator;
use taco_threshold_automaton::{
    ThresholdAutomaton,
    expressions::{Location, Parameter, Variable},
    path::Configuration,
};

use crate::{
    SMTExpr, SMTSolution, SMTSolver,
    expression_encoding::{DeclaresVariable, SMTSolverError, SMTVariableContext},
};

/// Trait for Context
pub trait ConfigFromSMT:
    SMTVariableContext<Parameter> + SMTVariableContext<Location> + SMTVariableContext<Variable>
{
    /// Extract the assignment found by the SMT solver
    fn get_assigned_configuration(
        &self,
        solver: &mut SMTSolver,
        res: SMTSolution,
    ) -> Result<Configuration, SMTSolverError> {
        if !res.is_sat() {
            return Err(SMTSolverError::ExtractionFromUnsat);
        }

        let var_assignment = self.get_solution(solver, res)?;
        let loc_assignment = self.get_solution(solver, res)?;

        Ok(Configuration::new(var_assignment, loc_assignment))
    }
}

/// SMT context for a configuration of a threshold automaton
#[derive(Debug, Clone)]
pub struct ConfigCtx {
    /// index of the configuration
    index: usize,
    /// reference to parameter variables
    params: Rc<HashMap<Parameter, SMTExpr>>,
    /// location variables
    loc_vars: HashMap<Location, SMTExpr>,
    /// variable variables
    variable_vars: HashMap<Variable, SMTExpr>,
}

impl ConfigCtx {
    /// Create a new set of variables for a configuration of the given threshold
    /// automaton
    pub fn new(
        solver: &mut SMTSolver,
        ta: &impl ThresholdAutomaton,
        params: Rc<HashMap<Parameter, SMTExpr>>,
        index: usize,
    ) -> ConfigCtx {
        let loc_vars = ta
            .locations()
            .map(|l| {
                let loc = l
                    .declare_variable(solver, index as u32)
                    .expect("Failed to declare locations");

                solver
                    .assert(solver.gte(loc, solver.numeral(0)))
                    .expect("Failed to assume loc >= 0");

                (l.clone(), loc)
            })
            .collect();

        let variable_vars = ta
            .variables()
            .map(|v| {
                let var = v
                    .declare_variable(solver, index as u32)
                    .expect("Failed to declare variables");

                solver
                    .assert(solver.gte(var, solver.numeral(0)))
                    .expect("Failed to assume var >= 0");

                (v.clone(), var)
            })
            .collect();

        Self {
            index,
            params,
            loc_vars,
            variable_vars,
        }
    }
}

impl ConfigFromSMT for ConfigCtx {}

impl SMTVariableContext<Parameter> for ConfigCtx {
    fn get_expr_for(&self, expr: &Parameter) -> Result<SMTExpr, SMTSolverError> {
        self.params
            .get(expr)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredParameter(expr.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Parameter>
    where
        Parameter: 'a,
    {
        self.params.keys()
    }
}

impl SMTVariableContext<Location> for ConfigCtx {
    fn get_expr_for(&self, expr: &Location) -> Result<SMTExpr, SMTSolverError> {
        self.loc_vars
            .get(expr)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredLocation(expr.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Location>
    where
        Location: 'a,
    {
        self.loc_vars.keys()
    }
}

impl SMTVariableContext<Variable> for ConfigCtx {
    fn get_expr_for(&self, expr: &Variable) -> Result<SMTExpr, SMTSolverError> {
        self.variable_vars
            .get(expr)
            .ok_or_else(|| SMTSolverError::UndeclaredVariable(expr.clone()))
            .cloned()
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Variable>
    where
        Variable: 'a,
    {
        self.variable_vars.keys()
    }
}

impl fmt::Display for ConfigCtx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(core::format_args!(
            "ConfigCtx {}: Locations: [ {} ], Variables: [ {} ]",
            self.index,
            join_iterator(self.loc_vars.keys(), ", "),
            join_iterator(self.variable_vars.keys(), ", "),
        ))
    }
}

#[cfg(test)]
mod tests {

    use std::{collections::HashMap, rc::Rc};

    use taco_threshold_automaton::{
        expressions::{Location, Parameter, Variable},
        general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder,
        path::Configuration,
    };

    use crate::{
        SMTSolverBuilder, SMTSolverContext,
        expression_encoding::{
            DeclaresVariable, SMTSolverError, SMTVariableContext, config_ctx::ConfigFromSMT,
        },
    };

    use super::ConfigCtx;

    #[test]
    fn test_all_variables_declared() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_parameters([Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .build();

        let mut solver = SMTSolverBuilder::default().new_solver();

        let n = solver
            .declare_const(Parameter::new("n").get_name(0), solver.int_sort())
            .unwrap();
        let f = solver
            .declare_const(Parameter::new("f").get_name(0), solver.int_sort())
            .unwrap();

        let params = Rc::new(HashMap::from([
            (Parameter::new("n"), n),
            (Parameter::new("f"), f),
        ]));

        let cfg = ConfigCtx::new(&mut solver, &ta, params, 0);

        assert!(cfg.get_expr_for(&Location::new("loc1")).is_ok());
        assert!(cfg.get_expr_for(&Location::new("loc2")).is_ok());
        assert!(cfg.get_expr_for(&Location::new("loc3")).is_ok());

        assert!(cfg.get_expr_for(&Variable::new("var1")).is_ok());
        assert!(cfg.get_expr_for(&Variable::new("var2")).is_ok());
        assert!(cfg.get_expr_for(&Variable::new("var3")).is_ok());

        assert!(cfg.get_expr_for(&Parameter::new("n")).is_ok());
        assert!(cfg.get_expr_for(&Parameter::new("f")).is_ok());
    }

    #[test]
    fn test_get_assigned_config() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_parameters([Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .build();

        let mut solver = SMTSolverBuilder::default().new_solver();

        let params = Rc::new(HashMap::new());

        let cfg = ConfigCtx::new(&mut solver, &ta, params, 0);

        let loc1_constr = solver.eq(
            cfg.get_expr_for(&Location::new("loc1")).unwrap(),
            solver.numeral(1),
        );
        let loc2_constr = solver.eq(
            cfg.get_expr_for(&Location::new("loc2")).unwrap(),
            solver.numeral(2),
        );
        let loc3_constr = solver.eq(
            cfg.get_expr_for(&Location::new("loc3")).unwrap(),
            solver.numeral(3),
        );

        let var1_constr = solver.eq(
            cfg.get_expr_for(&Variable::new("var1")).unwrap(),
            solver.numeral(1),
        );
        let var2_constr = solver.eq(
            cfg.get_expr_for(&Variable::new("var2")).unwrap(),
            solver.numeral(2),
        );
        let var3_constr = solver.eq(
            cfg.get_expr_for(&Variable::new("var3")).unwrap(),
            solver.numeral(3),
        );

        let smt_expr = solver.and_many([
            loc1_constr,
            loc2_constr,
            loc3_constr,
            var1_constr,
            var2_constr,
            var3_constr,
        ]);

        let res = solver.assert_and_check_expr(smt_expr).unwrap();

        let got_cfg = cfg.get_assigned_configuration(&mut solver, res).unwrap();

        let expected_cfg = Configuration::new(
            HashMap::from([
                (Variable::new("var1"), 1),
                (Variable::new("var2"), 2),
                (Variable::new("var3"), 3),
            ]),
            HashMap::from([
                (Location::new("loc1"), 1),
                (Location::new("loc2"), 2),
                (Location::new("loc3"), 3),
            ]),
        );

        assert_eq!(got_cfg, expected_cfg)
    }

    #[test]
    fn test_get_assigned_config_unsat() {
        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_locations([
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ])
            .unwrap()
            .with_parameters([Parameter::new("n"), Parameter::new("f")])
            .unwrap()
            .with_variables([
                Variable::new("var1"),
                Variable::new("var2"),
                Variable::new("var3"),
            ])
            .unwrap()
            .initialize()
            .build();

        let mut solver = SMTSolverBuilder::default().new_solver();

        let params = Rc::new(HashMap::new());

        let cfg = ConfigCtx::new(&mut solver, &ta, params, 0);

        let smt_expr = solver.false_();

        let res = solver.assert_and_check_expr(smt_expr).unwrap();

        let got_cfg = cfg.get_assigned_configuration(&mut solver, res);

        assert!(got_cfg.is_err());
        assert!(matches!(
            got_cfg.unwrap_err(),
            SMTSolverError::ExtractionFromUnsat
        ))
    }

    #[test]
    fn test_display_config_ctx() {
        let cfg = ConfigCtx {
            index: 42,
            params: Rc::new(HashMap::new()),
            loc_vars: HashMap::new(),
            variable_vars: HashMap::new(),
        };

        assert!(format!("{cfg}").contains("ConfigCtx"));
        assert!(format!("{cfg}").contains("42"));
    }
}

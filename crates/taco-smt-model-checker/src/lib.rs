//! This module implements the encoding of query on threshold automata into SMT
//! expressions. The algorithm is based on the encoding described in the paper
//! ["Complexity of Verification and Synthesis of Threshold Automata"](https://arxiv.org/abs/2002.08507)
//! by A. R. Balasubramanian, Javier Esparza, Marijana Lazic.
//!
//! The paper does not provide a complete encoding of the threshold automata,
//! instead many implementation details are not provided. As we were not
//! provided with the source code (nor an executable) of the implementation used
//! in the paper, we  had to make some assumptions about the implementation
//! details.
//!
//! We will explicitly mark functions that are not directly described in the
//! paper.

use core::fmt;
use std::error;

use log::info;
use smt_encoding::{ContextMgrError, EContextMgr};
use taco_model_checker::{
    ModelChecker, ModelCheckerResult, TargetSpec,
    reachability_specification::{DisjunctionTargetConfig, ReachabilityProperty},
};
use taco_smt_encoder::SMTSolverBuilder;
use taco_threshold_automaton::{
    ThresholdAutomaton, general_threshold_automaton::GeneralThresholdAutomaton,
};

#[cfg(feature = "parallel")]
use futures::StreamExt;
#[cfg(feature = "parallel")]
use futures::stream::FuturesUnordered;
#[cfg(feature = "parallel")]
use std::sync::{Arc, atomic::AtomicUsize};
#[cfg(feature = "parallel")]
use std::{collections::HashMap, sync::atomic::Ordering};
#[cfg(feature = "parallel")]
use taco_threshold_automaton::path::Path;
#[cfg(feature = "parallel")]
use tokio::runtime::Builder;
#[cfg(feature = "parallel")]
use tokio::task::JoinHandle;

pub mod smt_encoding;

/// Options to the SMT model checker
#[derive(Debug, Clone, PartialEq, Default)]
pub struct SMTModelCheckerOptions {
    /// Enable concurrent model checking (default: false / off)
    #[cfg(feature = "parallel")]
    parallel: bool,
}

impl SMTModelCheckerOptions {
    #[cfg(feature = "parallel")]
    pub fn new_parallel() -> Self {
        Self { parallel: true }
    }

    #[cfg(feature = "parallel")]
    pub fn new(parallel: bool) -> Self {
        Self { parallel }
    }
}

/// Errors that can occur during the initialization of the SMT model checker
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SMTModelCheckerInitializationError {
    /// Threshold automaton has decrements or resets
    ResetsOrDecrements,
}

impl fmt::Display for SMTModelCheckerInitializationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SMTModelCheckerInitializationError::ResetsOrDecrements => {
                write!(f, "Threshold automaton has decrements or resets")
            }
        }
    }
}

impl error::Error for SMTModelCheckerInitializationError {}

#[derive(Debug, Clone)]
pub struct SMTModelChecker {
    _opts: SMTModelCheckerOptions,
    solver_builder: SMTSolverBuilder,
    ta_spec: Vec<(DisjunctionTargetConfig, Vec<GeneralThresholdAutomaton>)>,
}

impl ModelChecker for SMTModelChecker {
    type ModelCheckerContext = SMTSolverBuilder;

    type ModelCheckerOptions = SMTModelCheckerOptions;

    type SpecType = ReachabilityProperty;

    type ThresholdAutomatonType = GeneralThresholdAutomaton;

    type InitializationError = SMTModelCheckerInitializationError;

    type ModelCheckingError = ContextMgrError;

    fn initialize(
        opts: Self::ModelCheckerOptions,
        ta_spec: Vec<(DisjunctionTargetConfig, Vec<Self::ThresholdAutomatonType>)>,
        ctx: Self::ModelCheckerContext,
    ) -> Result<Self, Self::InitializationError> {
        if ta_spec
            .iter()
            .any(|(_, tas)| tas.iter().any(|ta| ta.has_decrements_or_resets()))
        {
            return Err(SMTModelCheckerInitializationError::ResetsOrDecrements);
        }

        Ok(Self {
            _opts: opts,
            solver_builder: ctx,
            ta_spec,
        })
    }

    fn verify(
        self,
        abort_on_violation: bool,
    ) -> Result<taco_model_checker::ModelCheckerResult, Self::ModelCheckingError> {
        #[cfg(feature = "parallel")]
        if self._opts.parallel {
            return self.model_check_concurrent(abort_on_violation);
        }

        self.model_check_non_concurrent(abort_on_violation)
    }
}

impl SMTModelChecker {
    /// Execute the model checker sequentially
    fn model_check_non_concurrent(
        self,
        abort_on_violation: bool,
    ) -> Result<ModelCheckerResult, ContextMgrError> {
        let mut unsafe_prop = Vec::new();

        for (target, tas_to_check) in self.ta_spec.into_iter() {
            info!(
                "Starting to check property '{}', which requires {} model checker run(s).",
                target.name(),
                tas_to_check.len()
            );
            let mut found_counter_ex = false;
            for ta in tas_to_check.into_iter() {
                let target_var_constr = target
                    .get_variable_constraint()
                    .into_iter()
                    .collect::<Vec<_>>();

                let ctx_mgr = EContextMgr::new(ta, &target_var_constr, &self.solver_builder)?;
                let res = ctx_mgr.check_spec(&target);
                if let Some(p) = res {
                    info!("Property {} is not satisfied!", target.name());

                    unsafe_prop.push((target.name().to_string(), Box::new(p)));

                    if abort_on_violation {
                        return Ok(ModelCheckerResult::UNSAFE(unsafe_prop));
                    }

                    found_counter_ex = true;
                    break;
                }
            }

            if !found_counter_ex {
                info!(
                    "Finished verifying property '{}'. The property holds!",
                    target.name()
                );
            }
        }

        if !unsafe_prop.is_empty() {
            return Ok(ModelCheckerResult::UNSAFE(unsafe_prop));
        }

        Ok(ModelCheckerResult::SAFE)
    }

    #[cfg(feature = "parallel")]
    /// Verify all properties concurrently
    ///
    /// This method will build a multi-threaded runtime and will attempt to
    /// check each property concurrently to attempt to reduce the overall
    /// runtime.
    ///
    /// TODO: The setup is still very rudimentary and could be fine tuned in the
    /// future
    fn model_check_concurrent(
        self,
        abort_on_violation: bool,
    ) -> Result<ModelCheckerResult, ContextMgrError> {
        use std::collections::HashMap;

        let runtime = Builder::new_multi_thread()
            .thread_name("taco-smt-mc")
            .build()
            .unwrap();

        let mut completed_map = HashMap::new();

        let futures = FuturesUnordered::new();
        for (target, tas_to_check) in self.ta_spec.into_iter() {
            info!(
                "Queuing checks for property '{}', which requires {} model checker run(s).",
                target.name(),
                tas_to_check.len()
            );

            let completed_safe_counter = Arc::new(AtomicUsize::new(0));
            completed_map.insert(
                target.name().to_string(),
                (tas_to_check.len(), completed_safe_counter.clone()),
            );

            for ta in tas_to_check.into_iter() {
                let ft = runtime.spawn(Self::check_single_target(
                    ta,
                    target.clone(),
                    self.solver_builder.clone(),
                    completed_safe_counter.clone(),
                ));
                futures.push(ft.into_future());
            }
        }

        let res = runtime.spawn(Self::wait_for_mc_results(
            futures,
            abort_on_violation,
            completed_map,
        ));
        runtime
            .block_on(res)
            .expect("Task panicked or runtime error")
    }

    #[cfg(feature = "parallel")]
    /// Helper method to collect the results and abort early if desired
    ///
    // TODO: early abort is currently not working. It would require rewriting
    // the model checker in an asynchronous fashion
    async fn wait_for_mc_results(
        mut futures: FuturesUnordered<JoinHandle<Result<ModelCheckerResult, ContextMgrError>>>,
        abort_on_violation: bool,
        completed_map: HashMap<String, (usize, Arc<AtomicUsize>)>,
    ) -> Result<ModelCheckerResult, ContextMgrError> {
        let mut found_violations: Vec<(String, Box<Path>)> = Vec::new();

        while let Some(result) = futures.next().await {
            let res = result.expect("Task panicked or runtime error")?;

            if let ModelCheckerResult::UNSAFE(mut violations) = res {
                if abort_on_violation {
                    futures.into_iter().for_each(|f| {
                        f.abort();
                    });
                    return Ok(ModelCheckerResult::UNSAFE(violations));
                }
                found_violations.append(&mut violations);
            }
        }

        for (property_name, (expected_safe, terminated_safe)) in completed_map {
            if expected_safe == terminated_safe.load(Ordering::SeqCst) {
                info!("Finished verifying property '{property_name}'. The property holds!")
            }
        }

        if !found_violations.is_empty() {
            return Ok(ModelCheckerResult::UNSAFE(found_violations));
        }

        Ok(ModelCheckerResult::SAFE)
    }

    #[cfg(feature = "parallel")]
    /// Check reachability of a single [`DisjunctionTargetConfig`]
    async fn check_single_target(
        ta: GeneralThresholdAutomaton,
        target: DisjunctionTargetConfig,
        solver_builder: SMTSolverBuilder,
        safe_counter: Arc<AtomicUsize>,
    ) -> Result<ModelCheckerResult, ContextMgrError> {
        let target_var_constr = target
            .get_variable_constraint()
            .into_iter()
            .collect::<Vec<_>>();

        let ctx_mgr = EContextMgr::new(ta, &target_var_constr, &solver_builder)?;
        let res = ctx_mgr.check_spec(&target);

        if let Some(p) = res {
            info!("Property {} is not satisfied!", target.name());

            return Ok(ModelCheckerResult::UNSAFE(vec![(
                target.name().to_string(),
                Box::new(p),
            )]));
        }

        safe_counter.fetch_add(1, Ordering::SeqCst);
        Ok(ModelCheckerResult::SAFE)
    }
}

impl Default for SMTModelChecker {
    fn default() -> Self {
        Self::new_mc()
    }
}

impl SMTModelChecker {
    pub fn new_mc() -> Self {
        Self {
            _opts: SMTModelCheckerOptions::default(),
            solver_builder: SMTSolverBuilder::default(),
            ta_spec: Vec::new(),
        }
    }

    pub fn new_mc_with_opts(opts: SMTModelCheckerOptions) -> Self {
        Self {
            _opts: opts,
            solver_builder: SMTSolverBuilder::default(),
            ta_spec: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use taco_model_checker::{ModelChecker, reachability_specification::TargetConfig};
    use taco_parser::{ParseTA, ParseTAWithLTL, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilderCfg;
    use taco_threshold_automaton::{
        ModifiableThresholdAutomaton,
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        general_threshold_automaton::{Action, UpdateExpression, builder::RuleBuilder},
        path::{Configuration, PathBuilder, Transition},
    };

    #[test]
    fn test_can_initialize_true() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let spec = DisjunctionTargetConfig::new_from_targets(
            "test".into(),
            [TargetConfig::new_cover([Location::new("loc1")]).unwrap()],
        );

        let mc = SMTModelChecker::initialize(
            SMTModelCheckerOptions::default(),
            vec![(spec, vec![ta])],
            SMTSolverBuilder::default(),
        );
        assert!(mc.is_ok());
    }

    #[test]
    fn test_can_initialize_false() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do { var1' == 0; };
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let spec = DisjunctionTargetConfig::new_from_targets(
            "test".into(),
            [TargetConfig::new_cover([Location::new("loc1")]).unwrap()],
        );

        let mc = SMTModelChecker::initialize(
            SMTModelCheckerOptions::default(),
            vec![(spec, vec![ta])],
            SMTSolverBuilder::default(),
        );

        assert!(mc.is_err());
    }

    #[test]
    fn test_smt_model_checker_simple_unsafe() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc1 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let spec = DisjunctionTargetConfig::new_from_targets(
            "test".into(),
            [TargetConfig::new_cover([Location::new("loc1")]).unwrap()],
        );

        let mc = SMTModelChecker::initialize(
            SMTModelCheckerOptions::default(),
            vec![(spec, vec![ta])],
            SMTSolverBuilder::default(),
        )
        .unwrap();
        let res = mc.verify(true);
        assert!(res.is_ok());
        assert!(matches!(res.unwrap(), ModelCheckerResult::UNSAFE(_)));
    }

    #[cfg(feature = "parallel")]
    #[test]
    fn test_smt_model_checker_simple_unsafe_parallel() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc1 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let spec = DisjunctionTargetConfig::new_from_targets(
            "test".into(),
            [TargetConfig::new_cover([Location::new("loc1")]).unwrap()],
        );

        let mc = SMTModelChecker::initialize(
            SMTModelCheckerOptions::new_parallel(),
            vec![(spec, vec![ta])],
            SMTSolverBuilder::default(),
        )
        .unwrap();
        let res = mc.verify(true);
        assert!(res.is_ok());
        assert!(matches!(res.unwrap(), ModelCheckerResult::UNSAFE(_)));
    }

    #[test]
    fn test_smt_model_checker_simple_safe() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let spec = DisjunctionTargetConfig::new_from_targets(
            "test".into(),
            [TargetConfig::new_cover([Location::new("loc3")]).unwrap()],
        );

        let mc = SMTModelChecker::initialize(
            SMTModelCheckerOptions::default(),
            vec![(spec, vec![ta])],
            SMTSolverBuilder::default(),
        )
        .unwrap();
        let res = mc.verify(false);
        assert!(res.is_ok());
        assert!(matches!(res.unwrap(), ModelCheckerResult::SAFE));
    }

    #[cfg(feature = "parallel")]
    #[test]
    fn test_smt_model_checker_simple_safe_parallel() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0)
                }
            }
            ";

        let ta = ByMCParser::new().parse_ta(test_spec).unwrap();
        let spec = DisjunctionTargetConfig::new_from_targets(
            "test".into(),
            [TargetConfig::new_cover([Location::new("loc3")]).unwrap()],
        );

        let mc = SMTModelChecker::initialize(
            SMTModelCheckerOptions::new_parallel(),
            vec![(spec, vec![ta])],
            SMTSolverBuilder::default(),
        )
        .unwrap();
        let res = mc.verify(false);
        assert!(res.is_ok());
        assert!(matches!(res.unwrap(), ModelCheckerResult::SAFE));
    }

    #[test]
    fn test_smt_model_checker_simple_safe_new_mc() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0)
                }
            }
          ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();

        let mc = SMTModelChecker::new(
            Some(SMTSolverBuilderCfg::new_z3()),
            SMTModelCheckerOptions::default(),
            Vec::new(),
            ta,
            spec.expressions().iter().cloned(),
        )
        .expect("Failed to create SMT model checker");

        let res = mc.verify(false).expect("Failed to model check");
        assert!(matches!(res, ModelCheckerResult::SAFE));
    }

    #[cfg(feature = "parallel")]
    #[test]
    fn test_smt_model_checker_simple_safe_new_mc_parallel() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                }

                specifications (1) {
                    test1:
                        [](loc3 == 0)
                }
            }
          ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();

        let mc = SMTModelChecker::new(
            Some(SMTSolverBuilderCfg::new_z3()),
            SMTModelCheckerOptions::new_parallel(),
            Vec::new(),
            ta,
            spec.expressions().iter().cloned(),
        )
        .expect("Failed to create SMT model checker");

        let res = mc.verify(false).expect("Failed to model check");
        assert!(matches!(res, ModelCheckerResult::SAFE));
    }

    #[test]
    fn test_display_initialization_error() {
        let error = SMTModelCheckerInitializationError::ResetsOrDecrements;
        assert_eq!(
            format!("{error}"),
            "Threshold automaton has decrements or resets"
        );
    }

    #[test]
    fn test_full_model_checker_reach_location_three_rules_one_guard_self_loop_with_var_constr() {
        let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, f;
                
                assumptions (1) {
                    n > 3 * f;
                    n == 1;
                    f == 0;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f;
                    loc2 == 0;
                    loc3 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc1
                        when(true)
                        do {var1' == var1 + 1};
                    1: loc1 -> loc2
                        when(true)
                        do {};
                    2: loc2 -> loc3
                        when(var1 > 3 && var2 <= 0 && var1 < 6 )
                        do {};
                    
                }

                specifications (1) {
                    test1:
                        []((loc3 == 0) || (var1 < 5))
                }
            }
            ";

        let (ta, spec) = ByMCParser::new().parse_ta_and_spec(test_spec).unwrap();

        let mc = SMTModelChecker::new(
            Some(SMTSolverBuilderCfg::new_z3()),
            SMTModelCheckerOptions::new(false),
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();

        // Replicate spec ta that is created for ta builder
        let mut spec_ta = ta.clone();
        spec_ta.set_name("test_ta1-test1".into());

        // Replicate interval ta for path builder

        let path = PathBuilder::new(spec_ta)
            .add_parameter_assignment(HashMap::from([
                (Parameter::new("n"), 1),
                (Parameter::new("f"), 0),
            ]))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 0),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(0, Location::new("loc1"), Location::new("loc1"))
                    .with_action(Action::new_with_update(
                        Variable::new("var1"),
                        UpdateExpression::Inc(1),
                    ))
                    .build(),
                5,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 5),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 1),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(1, Location::new("loc1"), Location::new("loc2")).build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 5),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 1),
                    (Location::new("loc3"), 0),
                ]),
            ))
            .unwrap()
            .add_transition(Transition::new(
                RuleBuilder::new(2, Location::new("loc2"), Location::new("loc3"))
                    .with_guard(
                        BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Gt,
                            Box::new(IntegerExpression::Const(3)),
                        ) & BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                            ComparisonOp::Leq,
                            Box::new(IntegerExpression::Const(0)),
                        ) & BooleanExpression::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                            ComparisonOp::Lt,
                            Box::new(IntegerExpression::Const(6)),
                        ),
                    )
                    .build(),
                1,
            ))
            .unwrap()
            .add_configuration(Configuration::new(
                HashMap::from([
                    (Variable::new("var1"), 5),
                    (Variable::new("var2"), 0),
                    (Variable::new("var3"), 0),
                ]),
                HashMap::from([
                    (Location::new("loc1"), 0),
                    (Location::new("loc2"), 0),
                    (Location::new("loc3"), 1),
                ]),
            ))
            .unwrap()
            .build()
            .unwrap();

        let res = match res {
            ModelCheckerResult::SAFE => unreachable!("checked above"),
            ModelCheckerResult::UNSAFE(v) => {
                assert_eq!(v.len(), 1);
                *v[0].1.clone()
            }
            ModelCheckerResult::UNKNOWN(_) => todo!(),
        };

        assert_eq!(
            res,
            path.clone(),
            "Got:\n{}\n\nExpected:\n{}\n\n",
            res,
            path
        );
    }
}

//! Manager for configurations that build a path

use std::{cmp::min, collections::HashMap, rc::Rc};

use log::debug;
use taco_display_utils::join_iterator;
use taco_threshold_automaton::{
    RuleDefinition,
    expressions::Parameter,
    general_threshold_automaton::{GeneralThresholdAutomaton, Rule},
    path::{Configuration, InitializedPathBuilder, Path, PathBuilder, Transition},
};

use crate::{
    SMTExpr, SMTSolution, SMTSolver,
    expression_encoding::{SMTVariableContext, config_ctx::ConfigFromSMT, step_ctx::StepSMT},
};

/// Manager of configurations for a threshold automaton
pub struct SMTConfigMgr<CR, CC>
where
    CR: StepSMT,
    CC: ConfigFromSMT,
{
    params: Rc<HashMap<Parameter, SMTExpr>>,
    configs: Vec<Rc<CC>>,
    configs_primed: Vec<Rc<CC>>,
    step_steps: Vec<CR>,
    steady_steps: Vec<CR>,
}

impl<CR, CC> SMTConfigMgr<CR, CC>
where
    CR: StepSMT,
    CC: ConfigFromSMT,
{
    /// Create a new manager
    pub fn new(params: Rc<HashMap<Parameter, SMTExpr>>) -> Self {
        Self {
            params,
            configs: Vec::new(),
            configs_primed: Vec::new(),
            step_steps: Vec::new(),
            steady_steps: Vec::new(),
        }
    }

    /// Get a reference to the parameter variables
    pub fn params(&self) -> &Rc<HashMap<Parameter, SMTExpr>> {
        &self.params
    }

    /// Push a new steady configuration
    pub fn push_steady(&mut self, step_ctx: CR) {
        self.steady_steps.push(step_ctx);
    }

    /// Pop the last steady configuration
    pub fn pop_steady(&mut self) {
        self.steady_steps.pop();
    }

    /// Iterate over all steady steps
    pub fn steady(&self) -> impl Iterator<Item = &CR> {
        self.steady_steps.iter()
    }

    /// Push a new step
    pub fn push_step(&mut self, step_ctx: CR) {
        self.step_steps.push(step_ctx);
    }

    /// Pop a step
    pub fn pop_step(&mut self) {
        self.step_steps.pop();
    }

    /// Iterate over all steps
    pub fn step(&self) -> impl Iterator<Item = &CR> {
        self.step_steps.iter()
    }

    /// Push a new configuration
    pub fn push_cfg(&mut self, cfg_ctx: Rc<CC>) {
        self.configs.push(cfg_ctx);
    }

    /// Pop a configuration
    pub fn pop_cfg(&mut self) {
        self.configs.pop();
    }

    /// Iterate over all configurations
    pub fn configs(&self) -> impl Iterator<Item = &Rc<CC>> {
        self.configs.iter()
    }

    /// Iterate over all primed configurations
    pub fn configs_primed(&self) -> impl Iterator<Item = &Rc<CC>> {
        self.configs_primed.iter()
    }

    /// Push a new primed config
    pub fn push_cfg_primed(&mut self, cfg_ctx: Rc<CC>) {
        self.configs_primed.push(cfg_ctx);
    }

    /// Pop a primed config
    pub fn pop_cfg_primed(&mut self) {
        self.configs_primed.pop();
    }

    /// Extract the error path of the computed solution
    pub fn extract_error_path(
        &self,
        res: SMTSolution,
        solver: &mut SMTSolver,
        ta: GeneralThresholdAutomaton,
    ) -> Path {
        let builder = PathBuilder::new(ta);

        let param_assignment = self
            .params
            .get_solution(solver, res)
            .expect("Failed to extract parameter assignment for error path");
        let mut builder = builder
            .add_parameter_assignment(param_assignment)
            .expect("Parameter assignment returned by SMT solver invalid");

        for (i, ((config, config_primed), steady_step)) in self
            .configs
            .iter()
            .zip(self.configs_primed.iter())
            .zip(self.steady_steps.iter())
            .enumerate()
        {
            let config = config
                .get_assigned_configuration(solver, res)
                .expect("Failed to extract assigned configuration of config");

            builder = builder
                .add_configuration(config.clone())
                .expect("Configuration config extracted from SMT solver is invalid");

            builder = Self::add_transitions_steady_step_to_builder(
                builder,
                config,
                steady_step,
                solver,
                res,
            );

            let primed_config = config_primed
                .get_assigned_configuration(solver, res)
                .expect("Failed to extract assigned configuration of primed_config");

            builder = builder
                .add_configuration(primed_config)
                .expect("Configuration primed_config extracted from SMT solver is invalid");

            // Extract rules from current step step
            if i < self.step_steps.len() {
                builder = Self::add_transition_step_step_to_builder(
                    builder,
                    &self.step_steps[i],
                    solver,
                    res,
                );
            }
        }

        builder.build().expect("Extracted path is invalid!")
    }

    /// Compute the transition defined by a steady step and add them to the error
    /// path
    fn add_transitions_steady_step_to_builder(
        mut builder: InitializedPathBuilder,
        config: Configuration,
        steady_step: &CR,
        solver: &mut SMTSolver,
        res: SMTSolution,
    ) -> InitializedPathBuilder {
        let mut rules = steady_step
            .get_rules_applied(solver, res)
            .expect("Failed to extract rules used")
            .filter(|(_, n)| *n > 0)
            .collect::<Vec<_>>();

        let mut curr_config = config.clone();

        let old_rules = rules.clone();
        let old_config = config;

        // Try to order rules such that they are chainable
        while !rules.is_empty() {
            let mut n_apply = 0;

            // Add enabled self-loops first
            for (rule, n_to_apply) in rules.iter_mut().filter(|(r, _)| r.source() == r.target()) {
                if curr_config.get_processes_in_location(rule.source()) > 0 {
                    // if the transition is a self-loop apply it n_to_apply times
                    n_apply = *n_to_apply;
                    *n_to_apply = 0;

                    (builder, curr_config) =
                        Self::add_transition_to_builder_and_return_updated_config(
                            builder,
                            curr_config,
                            rule.clone(),
                            n_apply,
                        );
                }
            }

            for (rule, n_to_apply) in rules.iter_mut().filter(|(_, n)| *n > 0) {
                // Check if rule can be applied
                if curr_config.get_processes_in_location(rule.source()) > 0 {
                    // compute the number of times it can be applied
                    n_apply = min(
                        curr_config.get_processes_in_location(rule.source()),
                        *n_to_apply,
                    );

                    *n_to_apply -= n_apply;

                    (builder, curr_config) =
                        Self::add_transition_to_builder_and_return_updated_config(
                            builder,
                            curr_config,
                            rule.clone(),
                            n_apply,
                        );

                    // check if there are new self loops enabled after updating
                    // the configuration
                    break;
                }
            }

            assert!(
                n_apply > 0,
                "Failed to order rules into chainable order! Configuration that rules must be applied on:\n{}\n\nRules left to apply:\n{}\n\nSet of rules to be ordered in this steady step:\n{}\n\nInitial configuration of the steady step:\n{}\n\n ",
                curr_config,
                join_iterator(rules.iter().map(|(r, i)| format!("{i} x {r}")), ",\n"),
                join_iterator(old_rules.iter().map(|(r, i)| format!("{i} x {r}")), ",\n"),
                old_config,
            );

            rules.retain(|(_, n)| *n > 0);
        }

        builder
    }

    /// Create the transition that applies rule `rule` `n` times, compute the
    /// resulting configuration and add it to the path builder.
    /// Returns the computed configuration and updated builder.
    fn add_transition_to_builder_and_return_updated_config(
        mut builder: InitializedPathBuilder,
        config: Configuration,
        rule: Rule,
        n: u32,
    ) -> (InitializedPathBuilder, Configuration) {
        let transition = Transition::new(rule, n);
        let curr_config = config
            .apply_rule(&transition)
            .expect("Constructed transition invalid!");

        builder = builder
            .add_transition(transition)
            .expect("Failed to add transition to builder");
        builder = builder
            .add_configuration(curr_config.clone())
            .expect("Failed to add configuration computed in steady step");

        (builder, curr_config)
    }

    /// Compute the transition defined by a step step and add them to the error
    /// path
    fn add_transition_step_step_to_builder(
        builder: InitializedPathBuilder,
        step_step: &CR,
        solver: &mut SMTSolver,
        res: SMTSolution,
    ) -> InitializedPathBuilder {
        let mut rules_it = step_step
            .get_rules_applied(solver, res)
            .expect("Failed to extract rules applied");
        let applied_rule = rules_it.next();

        if applied_rule.is_none() {
            // skip this configuration since we might have already
            // reached an error
            debug!("Found an empty step step. Skipping!");
            return builder;
        }
        let (applied_rule, n) = applied_rule.unwrap();

        debug_assert!(
            rules_it.next().is_none(),
            "Expected only one rule to be applied in step step!"
        );

        debug_assert!(
            n == 1,
            "Expected rule in step step to be applied only once !"
        );

        let transition = Transition::new(applied_rule, 1);

        builder
            .add_transition(transition)
            .expect("Failed to add transition of step step to builder")
    }
}

//! Module for implementing advanced specification options for the model checker.
//!
//! This module ties together all potential configuration options, such as for
//! example BDD library or SMT checker options of the `TACO` model checker.

use taco_bdd::BDDManagerConfig;

use serde::Deserialize;

use taco_model_checker::preprocessing::ExistingPreprocessors;
use taco_smt_encoder::SMTSolverBuilderCfg;

/// Type representing configuration options for the `TACO` model checker
///
/// This struct contains options for the SMT solver and the BDD manager that can
/// be set using config files or environment variables. This type implements
/// `serde::Deserialize` to easily parse the configuration out of structured
/// configuration.
#[derive(Debug, Clone, Deserialize, Default)]
pub struct TACOConfig {
    /// Options for the SMT solver
    smt: Option<SMTSolverBuilderCfg>,
    /// Options for the BDD manager
    bdd: Option<BDDManagerConfig>,
    /// Options for configuring which preprocessors to use
    preprocessors: Option<Vec<ExistingPreprocessors>>,
}

impl TACOConfig {
    /// Set the configuration for the SMT solver builder to the given value
    pub fn set_smt_solver_builder_cfg(&mut self, cfg: SMTSolverBuilderCfg) {
        self.smt = Some(cfg);
    }

    /// Set the configuration for the BDD manager to the given value
    pub fn set_bdd_config(&mut self, cfg: BDDManagerConfig) {
        self.bdd = Some(cfg);
    }

    /// Get BDD manager and SMT solver builder configuration
    pub fn get_bdd_smt_config(&self) -> (Option<SMTSolverBuilderCfg>, Option<BDDManagerConfig>) {
        (self.smt.clone(), self.bdd.clone())
    }

    /// Get the SMT solver builder configuration
    pub fn get_smt_solver_builder_cfg(&self) -> Option<SMTSolverBuilderCfg> {
        self.smt.clone()
    }

    pub fn get_preprocessors_cfg(&self) -> &Option<Vec<ExistingPreprocessors>> {
        &self.preprocessors
    }
}

#[cfg(test)]
mod tests {

    use taco_bdd::BDDManagerConfig;
    use taco_model_checker::preprocessing::ExistingPreprocessors;
    use taco_smt_encoder::SMTSolverBuilderCfg;

    use crate::taco_config::TACOConfig;

    #[test]
    #[cfg(feature = "cudd")]
    fn test_taco_config() {
        let json_data = "{
            \"smt\": {
                \"command\": \"z3\"
            },
            \"bdd\": {
                \"Cudd\": []
            }
        }";

        let config: TACOConfig = serde_json::from_str(json_data).unwrap();

        let expected_smt = Some(SMTSolverBuilderCfg::new(
            "z3".to_string(),
            vec![],
            vec![],
            false,
        ));
        let expected_bdd = Some(BDDManagerConfig::new_cudd());

        assert_eq!(config.get_bdd_smt_config(), (expected_smt, expected_bdd));

        let smt_config = Some(SMTSolverBuilderCfg::new(
            "z3".to_string(),
            vec![],
            vec![],
            false,
        ));
        let bdd_config = Some(BDDManagerConfig::new_oxidd());

        let mut config = TACOConfig::default();
        config.set_smt_solver_builder_cfg(smt_config.clone().unwrap());
        config.set_bdd_config(bdd_config.clone().unwrap());
        assert_eq!(config.get_bdd_smt_config(), (smt_config, bdd_config));
    }

    #[test]
    fn test_taco_config_preprocessors() {
        let json_data = "{
            \"preprocessors\": [
                \"DropSelfLoops\",
                \"DropUnreachableLocations\",
                \"ReplaceTrivialGuardsStatic\",
                \"ReplaceTrivialGuardsSMT\",
                \"RemoveUnusedVariables\",
                \"DropUnsatisfiableRules\",
                \"CollapseLocations\"
            ]
        }";

        let config: TACOConfig = serde_json::from_str(json_data).unwrap();

        let expected_preprocessors = Some(vec![
            ExistingPreprocessors::DropSelfLoops,
            ExistingPreprocessors::DropUnreachableLocations,
            ExistingPreprocessors::ReplaceTrivialGuardsStatic,
            ExistingPreprocessors::ReplaceTrivialGuardsSMT,
            ExistingPreprocessors::RemoveUnusedVariables,
            ExistingPreprocessors::DropUnsatisfiableRules,
            ExistingPreprocessors::CollapseLocations,
        ]);

        assert_eq!(config.get_preprocessors_cfg(), &expected_preprocessors);
    }
}

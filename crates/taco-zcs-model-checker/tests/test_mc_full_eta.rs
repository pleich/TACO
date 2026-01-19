//! Tests for the full model checker, including checking paths for spuriosity
//!
//! These test test small benchmarks without resets that can be checked fast.

#[cfg(test)]
mod test_cs_mc_full {
    use std::fs;

    use taco_bdd::BDDManagerConfig;
    use taco_model_checker::ModelChecker;
    use taco_parser::{ParseTAWithLTL, bymc::ByMCParser};
    use taco_smt_encoder::SMTSolverBuilderCfg;
    use taco_zcs_model_checker::ZCSModelChecker;

    const RESET_BENCHMARK_FOLDER: &str = "../../benchmarks/reset-benchmarks";

    #[test]
    fn test_srb() {
        let file = RESET_BENCHMARK_FOLDER.to_string() + "/SRB.eta";
        let ta_str = fs::read_to_string(file.clone())
            .unwrap_or_else(|err| panic!("Failed to read file {}: {}", file, err));

        let parser = ByMCParser {};
        let (ta, spec) = parser
            .parse_ta_and_spec(&ta_str)
            .unwrap_or_else(|err| panic!("Failed to parse file {}: {}", file, err));
        let mc = ZCSModelChecker::new(
            Some((
                Some(SMTSolverBuilderCfg::new_z3()),
                Some(BDDManagerConfig::new_cudd()),
            )),
            None,
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();
        assert!(res.is_safe())
    }

    #[test]
    fn test_rb_relbrd_v1() {
        // let env = Env::default()
        //     .filter_or("MY_LOG_LEVEL", "info")
        //     .write_style_or("MY_LOG_STYLE", "always");
        // env_logger::init_from_env(env);

        let file = RESET_BENCHMARK_FOLDER.to_string() + "/rb-RelBrd_V1.eta";
        let ta_str = fs::read_to_string(file.clone())
            .unwrap_or_else(|err| panic!("Failed to read file {}: {}", file, err));

        let parser = ByMCParser {};
        let (ta, spec) = parser
            .parse_ta_and_spec(&ta_str)
            .unwrap_or_else(|err| panic!("Failed to parse file {}: {}", file, err));
        let mc = ZCSModelChecker::new(
            Some((
                Some(SMTSolverBuilderCfg::new_z3()),
                Some(BDDManagerConfig::new_cudd()),
            )),
            None,
            Vec::new(),
            ta.clone(),
            spec.into_iter(),
        );
        let mc = mc.unwrap();
        let res = mc.verify(true).unwrap();
        assert!(res.is_safe())
    }
}

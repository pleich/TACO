//! Integration tests for the transformation into a `AbstractThresholdAutomaton`.
use taco_parser::bymc::ByMCParser;
use taco_parser::*;

/// These tests check whether the benchmark files can be transformed by the lia
/// transformation.
mod transform_bymc_spec_files {

    use std::{env, fs, time::Instant};

    use taco_interval_ta::builder::IntervalTABuilder;

    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton;
    use walkdir::WalkDir;

    use super::{ByMCParser, ParseTA};

    const BYMC_BENCHMARK_FOLDER: &str = "../../benchmarks/TACO";

    /// This test will try to find all `.ta` recursively in the
    /// `BYMC_BENCHMARK_FOLDER` folder and will try to parse and transform them into
    /// a linear integer arithmetic threshold automaton.
    ///
    /// It does not check for correctness of the parsed automaton, but checks
    /// whether the transformation might have introduced comparison guards,
    /// which should not happen.
    #[test]
    fn test_all_bymc_benchmarks_can_be_transformed() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BYMC_BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let ta_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let got_ta = parser.parse_ta(&ta_str).unwrap();

                println!("Parsed successfully");

                println!("Transforming to LIA");
                let lia_ta = LIAThresholdAutomaton::try_from(got_ta).unwrap_or_else(|err| {
                    panic!(
                        "Failed to transform to LIA {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let solver_builder = SMTSolverBuilder::default();

                let interval_threshold_automaton_builder =
                    IntervalTABuilder::new(lia_ta, solver_builder, vec![]);

                println!("Building abstract threshold automata");
                let now = Instant::now();
                let interval_threshold_automatons = interval_threshold_automaton_builder.build();
                let elapsed = now.elapsed();

                println!(
                    "Successfully computed interval orders: {} automata to check in {}ms",
                    interval_threshold_automatons.unwrap().count(),
                    elapsed.as_millis()
                );
            }
        }

        println!("\nSuccessfully transformed all benchmarks into abstract threshold automata!");
    }
}

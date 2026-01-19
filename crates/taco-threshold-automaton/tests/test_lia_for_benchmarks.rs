//! Integration tests for the transformation into a `LIAThresholdAutomaton`.
use taco_parser::bymc::ByMCParser;
use taco_parser::*;

/// These tests check whether the benchmark files can be transformed by the lia
/// transformation.
mod transform_bymc_spec_files {

    use std::{env, fs};

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
                let got_ta = parser.parse_ta(&ta_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed successfully");

                println!("Transforming to LIA");
                let got_lia_ta = LIAThresholdAutomaton::try_from(got_ta).unwrap_or_else(|err| {
                    panic!(
                        "Failed to transform to LIA {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!(
                    "Automaton has {} distinct thresholds, with {} being constant",
                    got_lia_ta.get_thresholds().len(),
                    got_lia_ta
                        .get_thresholds()
                        .into_iter()
                        .filter(|t| t.is_constant())
                        .count()
                );
                println!("Transformed successfully");

                println!("Checking whether the transformed automata contain comparison guards");
                assert!(!got_lia_ta.has_comparison_guard());

                println!("No such guards detected.\n");
            }
        }

        println!("\nSuccessfully transformed all benchmarks to LIA!");
    }
}

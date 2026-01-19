//! Integration tests for the `bymc` parser.
use taco_parser::bymc::ByMCParser;
use taco_parser::*;

/// These tests check whether the benchmark files are accepted by the
/// bymc parser.
mod parse_bymc_spec_files {

    use std::{env, fs};

    use taco_parser::ParseTAWithLTL;
    use walkdir::WalkDir;

    use super::ByMCParser;

    const BENCHMARK_FOLDER: &str = "../../benchmarks/TACO";

    /// This test will try to find all `.ta` recursively in the
    /// `BENCHMARK_FOLDER` folder.
    /// It does not check for correctness of the parsed automaton but only that the parser does accept the file.
    #[test]
    fn test_all_benchmarks_can_be_parsed() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(BENCHMARK_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".ta") {
                println!("Checking file {f_name}");

                let spec_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = ByMCParser {};
                let _got_ta = parser.parse_ta_and_spec(&spec_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse threshold automaton from file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed LTL specification successfully");
            }
        }
    }
}

/// These tests check whether the parser correctly propagates error that usually
/// come from the Builder.
mod integration_builder_parser_errors {

    use super::*;

    #[test]
    fn parse_full_ta_unknown_param_in_rc() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (0) {
                    n >= 1;
                    uk = 2;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                    when (true)
                    do { sha' == sha + 1 };
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }

    #[test]
    fn parse_full_ta_unknown_in_inits() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (0) {
                    n >= 1;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                    uk = 2;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                    when (true)
                    do { sha' == sha + 1 };
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }

    #[test]
    fn parse_full_ta_unknown_loc_in_rule() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (0) {
                    n >= 1;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                    when (true)
                    do { sha' == sha + 1 };
                    1: q0 -> uk
                    when (false)
                    do { sha' == sha + 1 };
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }

    #[test]
    fn parse_full_ta_unknown_var_in_rule_guard() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (0) {
                    n >= 1;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                    when (uk > 1)
                    do { sha' == sha + 1 };
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }

    #[test]
    fn parse_full_ta_unknown_var_in_rule_update() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (0) {
                    n >= 1;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                    when (true)
                    do { sha' == sha + 1 ; reset(uk)};
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }

    #[test]
    fn parse_full_ta_double_id() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (0) {
                    n >= 1;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                        when (true)
                        do { sha' == sha + 1 };
                    0: q0 -> q2
                        when (false)
                        do { sha' == sha + 1 };
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }

    #[test]
    fn parse_full_ta_invalid_act() {
        let test_spec = "
            skel test_ta {
                local loc;
                shared sha, sha2;
                parameters n;

                assumptions (0) {
                    n >= 1;
                }

                locations (0) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/

                inits (0) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */

                rules (0) {
                    0: q0 -> q1
                        when (true)
                        do { sha' == sha2 + 1 };
                    0: q0 -> q2
                        when (false)
                        do { sha' == sha + 1 };
                }

                specifications (5) {}
            }
            ";

        let parser = ByMCParser {};
        let got_ta = parser.parse_ta(test_spec);

        assert!(got_ta.is_err())
    }
}

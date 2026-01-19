//! This module contains the logic to output a GeneralThresholdAutomaton into
//! a specific format

use taco_display_utils::indent_all;
use taco_model_checker::eltl::ELTLSpecification;
use taco_threshold_automaton::{
    ThresholdAutomaton, general_threshold_automaton::GeneralThresholdAutomaton,
};

/// Translate a [GeneralThresholdAutomaton] and [ELTLSpecification] into ByMC
/// specification
pub fn into_bymc(ta: &GeneralThresholdAutomaton, spec: &ELTLSpecification) -> String {
    let ta_body = ta.get_ta_body_in_bymc_format();
    let spec = spec.to_string();

    let ta_full = ta_body + "\n\n" + &spec;

    format!(
        "thresholdAutomaton {} {{\n{}\n}}\n",
        ta.name(),
        indent_all(ta_full)
    )
}

/// Translate a [GeneralThresholdAutomaton] and [ELTLSpecification] into TLA+
/// specification
///
// TODO: implement
pub fn into_tla(_ta: &GeneralThresholdAutomaton, _spec: &ELTLSpecification) -> String {
    unimplemented!("TLA+ conversion has not been implemented yet :(")
}

#[cfg(test)]
mod tests {
    use std::{env, fs};

    use taco_parser::{ParseTAWithLTL, bymc::ByMCParser, tla::TLAParser};
    use walkdir::WalkDir;

    use crate::cli::output_formats::{into_bymc, into_tla};

    const EXAMPLES_FOLDER: &str = "../../examples/tla";

    #[test]
    fn test_all_examples_translate_valid() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(EXAMPLES_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".tla") {
                println!("Checking file {f_name}");

                let spec_str = fs::read_to_string(entry.path()).unwrap();

                let parser = TLAParser {};
                let (ta, spec) = parser.parse_ta_and_spec(&spec_str).unwrap();

                let new_input = into_bymc(&ta, &spec);

                let bymc_parser = ByMCParser;
                let (new_ta, new_spec) = bymc_parser.parse_ta_and_spec(&new_input).unwrap();

                assert_eq!(ta, new_ta);
                assert_eq!(spec, new_spec);

                println!("Parsed TLA specification successfully");
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_into_tla() {
        println!("Start {}", env::current_dir().unwrap().display());

        for entry in WalkDir::new(EXAMPLES_FOLDER)
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let f_name = entry.file_name().to_string_lossy();
            println!("Found file or folder {}", entry.path().to_string_lossy());

            if f_name.ends_with(".tla") {
                println!("Checking file {f_name}");

                let spec_str = fs::read_to_string(entry.path()).unwrap();

                let parser = ByMCParser {};
                let (ta, spec) = parser.parse_ta_and_spec(&spec_str).unwrap();

                let new_input = into_tla(&ta, &spec);

                let bymc_parser = TLAParser {};
                let (new_ta, new_spec) = bymc_parser.parse_ta_and_spec(&new_input).unwrap();

                assert_eq!(ta, new_ta);
                assert_eq!(spec, new_spec);

                println!("Parsed TLA specification successfully");
            }
        }
    }
}

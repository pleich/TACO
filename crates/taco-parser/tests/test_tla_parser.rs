//! Tests for the TLA+ parser

#[cfg(test)]
mod test_tla_parser {
    use std::{env, fs};

    use taco_parser::{ParseTAWithLTL, tla::TLAParser};
    use walkdir::WalkDir;

    const EXAMPLES_FOLDER: &str = "../../examples/tla";

    #[test]
    fn test_all_examples_can_be_parsed() {
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

                let spec_str = fs::read_to_string(entry.path()).unwrap_or_else(|err| {
                    panic!(
                        "Failed to read file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                let parser = TLAParser {};
                let (_got_ta, _ltl) = parser.parse_ta_and_spec(&spec_str).unwrap_or_else(|err| {
                    panic!(
                        "Failed to parse threshold automaton from file {}: {}",
                        entry.path().to_string_lossy(),
                        err
                    )
                });

                println!("Parsed TLA specification successfully");
            }
        }
    }
}

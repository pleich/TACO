//! TACO Command Line Interface
//!
//! This crate contains the TACO CLI that can be used to verify, translate and
//! visualize different flavors of threshold automata. Consult the TACO
//! documentation for more information on how to use the tool, what
//! specification formats are supported etc.

use ::config::Config;

use clap::Parser;
use cli::get_bdd_manager_cfg;
#[cfg(feature = "dot")]
use cli::visualize_ta;
use cli::{Cli, initialize_logger, parse_input_file};
use human_panic::setup_panic;
use log::{debug, info};
use taco_model_checker::eltl::ELTLSpecificationBuilder;
use taco_threshold_automaton::ThresholdAutomaton;

use crate::cli::{
    create_coverability_expression, create_reachability_expression, get_smt_solver,
    parse_coverability, parse_reachability, translate_ta,
};
mod cli;
mod taco_config;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    setup_panic!();

    // parse the cli arguments
    let cli = Cli::parse();
    initialize_logger(cli.log_config)?;
    info!("Welcome to the TACO model checker!");
    match cli.command {
        cli::Commands::Check {
            input,
            config_file,
            model_checker,
            bdd,
            smt_solver,
            compact_out,
            abort_on_violation,
            mode,
        } => {
            let (mut ta, mut spec) = parse_input_file(input)?;

            info!(
                "Parsed threshold automaton with the name '{}' from the input file",
                ta.name()
            );
            debug!("Parsed threshold automaton: {ta}");

            let n_loc = ta.locations().count();
            let n_rules = ta.rules().count();
            info!("Threshold automaton has {n_loc} locations and {n_rules} rules");

            // Check whether a configuration file was supplied
            let mut settings = Config::builder();
            if let Some(config_file) = config_file {
                if !config_file.exists() {
                    return Err(anyhow::anyhow!(
                        "Specified configuration file '{}' does not exist.",
                        config_file.display()
                    )
                    .into());
                }

                settings = settings.add_source(config::File::from(config_file));
            }

            // Parse configuration from environment variables
            settings = settings.add_source(config::Environment::with_prefix("TACO"));
            let mut config = settings
                .build()?
                .try_deserialize::<taco_config::TACOConfig>()?;

            // Check whether the smt solver was overridden via CLI
            if let Some(solver) = smt_solver {
                let solver_cfg = get_smt_solver(solver);
                config.set_smt_solver_builder_cfg(solver_cfg);
            }

            // Check whether the bdd manager was overridden via CLI
            if let Some(bdd) = bdd {
                let bdd_cfg = get_bdd_manager_cfg(bdd);
                config.set_bdd_config(bdd_cfg);
            }

            // Check whether we want a check based on the input file or a quick
            // coverability or reachability check through the CLI
            match mode {
                cli::CheckMode::Coverability => {
                    // Parse coverability
                    let loc_to_be_covered = parse_coverability(&mut ta);
                    // Build expression for specification and add it to the TA
                    let expression = create_coverability_expression(loc_to_be_covered);

                    let mut builder = ELTLSpecificationBuilder::new(&ta);
                    builder
                        .add_expression(String::from("coverability"), expression)
                        .unwrap();
                    spec = builder.build();
                }
                cli::CheckMode::Reachability => {
                    // Parse reachability
                    let (populated_locs, unpopulated_locs) = parse_reachability(&mut ta);
                    // Build expression for specification and add it to the TA
                    let expression =
                        create_reachability_expression(populated_locs, unpopulated_locs);
                    let mut builder = ELTLSpecificationBuilder::new(&ta);
                    builder
                        .add_expression(String::from("reachability"), expression)
                        .unwrap();
                    spec = builder.build();
                }
                _ => (),
            }

            cli::display_result(
                ta,
                spec,
                model_checker,
                config,
                abort_on_violation,
                mode,
                compact_out,
            );

            info!("Finished model checking. Goodbye!");
            Ok(())
        }

        #[cfg(feature = "dot")]
        cli::Commands::Visualize { input, output } => {
            let (ta, _) = parse_input_file(input)?;
            visualize_ta(&ta, output)?;
            Ok(())
        }
        cli::Commands::Translate { input, output } => {
            let (ta, spec) = parse_input_file(input)?;
            translate_ta(&ta, &spec, output)?;
            Ok(())
        }
    }
}

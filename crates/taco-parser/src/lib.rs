//! Traits for parsers that can parse specifications and threshold automata.
//!
//! This module contains traits that parsers for threshold automata and LTL
//! specifications should implement. The traits are:
//! - `ParseTA`, for parsing threshold automata,
//! - `ParseLTLSpec`, for parsing LTL specifications,
//! - `ParseTAWithLTL`, for parsing threshold automata and LTL specifications.

use anyhow::Error;
use taco_model_checker::eltl::ELTLSpecification;
use taco_threshold_automaton::general_threshold_automaton::GeneralThresholdAutomaton;

// The pest derive generates errors as the doc comments are missing
#[allow(missing_docs)]
pub mod bymc;

// The pest derive generates errors as the doc comments are missing
#[allow(missing_docs)]
pub mod tla;

/// Parse a threshold automaton from a string.
///
/// Parsers for threshold automata should implement this trait.
pub trait ParseTA {
    /// Try to parse the threshold automaton from a string.
    fn parse_ta(&self, input: &str) -> Result<GeneralThresholdAutomaton, Error>;
}

/// Parse a threshold automaton and an LTL specification from a string.
///
/// If you know a file or input includes both a threshold automaton and an LTL specification, prefer using this
/// trait. Parsers for threshold automata and LTL specifications should implement
/// this trait.
pub trait ParseTAWithLTL {
    /// Try to parse the threshold automaton and LTL specification from a string.
    ///
    /// Returns a tuple of the threshold automaton and the LTL specification.
    fn parse_ta_and_spec(
        &self,
        input: &str,
    ) -> Result<(GeneralThresholdAutomaton, ELTLSpecification), Error>;
}

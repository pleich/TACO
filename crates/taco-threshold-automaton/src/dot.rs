//! Visualization of threshold automata in DOT format
//!
//! This module provides the trait `ToDOT` for converting threshold automata into
//! the [DOT format](https://graphviz.org/doc/info/lang.html), which can be
//! visualized using tools like [Graphviz](https://graphviz.org/).
//!
//! The trait `ToDOT` is implemented for both `ThresholdAutomaton` and
//! `LIAThresholdAutomaton`. The `ThresholdAutomaton` can be converted into a
//! graph in DOT format, while the `LIAThresholdAutomaton` can be converted into
//! a graph in DOT format with the additional information of the transformed
//! guards.
//!
//! The trait `DOTDiff` is meant for debugging purposes and implemented for
//! both `ThresholdAutomaton` and `LIAThresholdAutomaton`. It allows to
//! visualize the difference between two automata in DOT format, i.e., it marks
//! added locations and edges in green, removed locations and edges in red, and
//! unchanged locations and edges in black.

use std::fmt::{self};

use taco_display_utils::{indent_all, join_iterator};

use crate::{RuleDefinition, ThresholdAutomaton};

/// Define the font type for labels and nodes in the graph
const GRAPH_OPTIONS: &str = "\
rankdir=LR \
fontname=\"Helvetica,Arial,sans-serif\" \
node [fontname=\"Helvetica,Arial,sans-serif\"] \
edge [fontname=\"Helvetica,Arial,sans-serif\"];";

/// Options to mark initial locations
const INITIAL_LOC_OPTIONS: &str = "shape = circle";
/// Options for locations
const LOC_OPTIONS: &str = "shape = circle";

// Diff coloring
/// Options for removed locations
const REMOVED: &str = "color = red, fontcolor = red";
/// Options for added locations
const ADDED: &str = "color = green, fontcolor = green";

/// Objects implementing this train can be converted visualized as a graph with
/// graphviz
///
/// This trait is only available if the `dot` feature is enabled. It allows to
/// export an object into the
/// [DOT format](https://graphviz.org/doc/info/lang.html),
/// which can be visualized using tools like [Graphviz](https://graphviz.org/).
pub trait ToDOT {
    /// Get the underlying graph in DOT format
    ///
    /// Returns the visualization in DOT format. The output can be visualized
    /// using tools [Graphviz](https://graphviz.org/) or tools compatible with
    /// the [DOT Language](https://graphviz.org/doc/info/lang.html).
    fn get_dot_graph(&self) -> String;
}

/// Trait for encoding an automaton (e.g.
/// [`crate::general_threshold_automaton::GeneralThresholdAutomaton`] or other
/// types implementing the [`ThresholdAutomaton`] trait into a graph in DOT
/// format
trait AutomatonEncoding {
    /// Type for the edge labels
    type EdgeLabel: fmt::Display + PartialEq;

    /// Name of the automaton
    fn get_name(&self) -> String;

    /// Initial locations of the automaton
    ///
    /// Locations are the states of the automaton and must implement
    /// `fmt::Display`. The name will be used as the label in the DOT file.
    fn get_initial_locations(&self) -> impl Iterator<Item = String>;

    /// Locations of the automaton
    ///
    /// Get the locations of the automaton that are neither initial nor final
    /// Locations must implement
    /// `fmt::Display`. The name will be used as the label in the DOT file.
    fn get_locations(&self) -> impl Iterator<Item = String>;

    /// Get the transitions of the automaton
    fn get_transitions(&self) -> impl Iterator<Item = (String, Self::EdgeLabel, String)>;

    /// Get the encoding of the nodes into the DOT format
    fn get_node_encoding(nodes: impl Iterator<Item = String>, node_options: &String) -> String {
        let mut nodes = join_iterator(nodes, "\n");
        if !nodes.is_empty() {
            nodes = format!("node [{}];\n{}\n;", node_options, indent_all(nodes));
            nodes = indent_all(nodes);
            nodes += "\n";
        }

        nodes
    }

    /// General function to enable the encoding of the edges into the DOT format
    /// with the given edge options
    fn get_edge_encoding(
        edges: impl Iterator<Item = (String, Self::EdgeLabel, String)>,
        edge_options: &String,
    ) -> String {
        let edge_options = if edge_options.is_empty() {
            String::new()
        } else {
            format!(", {edge_options}")
        };

        let edges = edges
            .map(|(src, label, tgt)| format!("{src} -> {tgt} [label = \"{label}\"{edge_options}]"));
        let mut edges = join_iterator(edges, ";\n");

        if !edges.is_empty() {
            edges += ";";
            edges = indent_all(edges);
            edges += "\n";
        }

        edges
    }
}

// implement `ToDOT` for all types implementing the [`AutomatonEncoding`] trait
impl<T: AutomatonEncoding> ToDOT for T {
    fn get_dot_graph(&self) -> String {
        let graph_title = format!(
            "graph [label =<<B>{}</B>>, labelloc = t, fontsize = 35];\n",
            self.get_name()
        );

        let init_states = Self::get_node_encoding(
            self.get_initial_locations(),
            &INITIAL_LOC_OPTIONS.to_string(),
        );

        let loc = Self::get_node_encoding(self.get_locations(), &LOC_OPTIONS.to_string());

        let transitions = Self::get_edge_encoding(self.get_transitions(), &String::new());

        format!(
            "digraph {} {{\n{}\n{}{}{}{}}}",
            self.get_name(),
            indent_all(GRAPH_OPTIONS),
            indent_all(graph_title),
            init_states,
            loc,
            transitions,
        )
    }
}

// implement [`AutomatonEncoding`] for all types implementing the
// [`ThresholdAutomaton`] type
impl<T> AutomatonEncoding for T
where
    T: ThresholdAutomaton,
{
    type EdgeLabel = String;

    fn get_name(&self) -> String {
        self.name().to_string()
    }

    fn get_initial_locations(&self) -> impl Iterator<Item = String> {
        self.locations()
            .filter(|l| self.can_be_initial_location(l))
            .map(|l| l.to_string())
    }

    fn get_locations(&self) -> impl Iterator<Item = String> {
        self.locations().map(|l| l.to_string())
    }

    fn get_transitions(&self) -> impl Iterator<Item = (String, Self::EdgeLabel, String)> {
        self.rules().map(|r| {
            (
                r.source().to_string(),
                r.guard().to_string(),
                r.target().to_string(),
            )
        })
    }
}

/// Visualize the difference between two objects in DOT format
///
/// This trait is only available if the `dot` feature is enabled. It allows to
/// visualize the difference between two objects in DOT format, i.e., it marks
/// added objects in green, removed objects in red, and unchanged locations and
/// edges in black.
pub trait DOTDiff {
    /// Get the difference between two objects in DOT format
    ///
    /// Returns the difference between two objects in DOT format, i.e., it marks
    /// added objects in green, removed objects in red, and unchanged locations and
    /// edges in black.
    fn get_dot_diff(&self, other: &Self) -> String;
}

impl<T: AutomatonEncoding> DOTDiff for T {
    fn get_dot_diff(&self, other: &Self) -> String {
        let graph_title = format!(
            "graph [label =<<B>Diff: {} - {} </B>>, labelloc = t, fontsize = 35];\n",
            self.get_name(),
            other.get_name()
        );

        let removed_init_states = self
            .get_initial_locations()
            .filter(|l| !other.get_initial_locations().any(|ol| *l == ol));
        let removed_init_states = Self::get_node_encoding(
            removed_init_states,
            &format!("{INITIAL_LOC_OPTIONS}, {REMOVED}"),
        );

        let added_init_states = other
            .get_initial_locations()
            .filter(|l| !self.get_initial_locations().any(|ol| *l == ol));
        let added_init_states = Self::get_node_encoding(
            added_init_states,
            &format!("{INITIAL_LOC_OPTIONS}, {ADDED}"),
        );

        let regular_init_states = self
            .get_initial_locations()
            .filter(|l| other.get_initial_locations().any(|ol| *l == ol));
        let regular_init_states =
            Self::get_node_encoding(regular_init_states, &INITIAL_LOC_OPTIONS.to_string());
        let init_states = format!("{removed_init_states}{added_init_states}{regular_init_states}");

        let removed_loc = self
            .get_locations()
            .filter(|l| !other.get_locations().any(|ol| *l == ol));
        let removed_loc =
            Self::get_node_encoding(removed_loc, &format!("{LOC_OPTIONS}, {REMOVED}"));

        let added_loc = other
            .get_locations()
            .filter(|l| !self.get_locations().any(|ol| *l == ol));
        let added_loc = Self::get_node_encoding(added_loc, &format!("{LOC_OPTIONS}, {ADDED}"));

        let regular_loc = self
            .get_locations()
            .filter(|l| other.get_locations().any(|ol| *l == ol));
        let regular_loc = Self::get_node_encoding(regular_loc, &LOC_OPTIONS.to_string());
        let loc = format!("{removed_loc}{added_loc}{regular_loc}");

        let removed_transitions = self.get_transitions().filter(|(src, lbl, tgt)| {
            !other
                .get_transitions()
                .any(|(osrc, olbl, otgt)| *src == osrc && *tgt == otgt && *lbl == olbl)
        });
        let removed_transitions =
            Self::get_edge_encoding(removed_transitions, &format!("{REMOVED}, {REMOVED}"));

        let added_transitions = other.get_transitions().filter(|(src, lbl, tgt)| {
            !self
                .get_transitions()
                .any(|(osrc, olbl, otgt)| *src == osrc && *tgt == otgt && *lbl == olbl)
        });
        let added_transitions =
            Self::get_edge_encoding(added_transitions, &format!("{ADDED}, {ADDED}"));

        let regular_transitions = self.get_transitions().filter(|(src, lbl, tgt)| {
            other
                .get_transitions()
                .any(|(osrc, olbl, otgt)| *src == osrc && *tgt == otgt && *lbl == olbl)
        });
        let regular_transitions = Self::get_edge_encoding(regular_transitions, &String::new());
        let transitions = format!("{removed_transitions}{added_transitions}{regular_transitions}");

        format!(
            "digraph {} {{\n{}\n{}{}{}{}}}",
            self.get_name(),
            indent_all(GRAPH_OPTIONS),
            indent_all(graph_title),
            init_states,
            loc,
            transitions,
        )
    }
}

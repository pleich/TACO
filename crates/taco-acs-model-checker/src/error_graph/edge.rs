//! Edge type for the error graph
//!
//! An edge in the [`super::ErrorGraph`] stores the ids of the rules that lead to the
//! successor node.
//!
//! This module only borrows a `NodeRef` when creating a new edge.

use std::collections::BTreeSet;

use crate::{
    acs_threshold_automaton::{CSRule, configuration::ACSTAConfig},
    error_graph::NodeRef,
};

/// Edge in the error graph
///
/// An edge in the error graph consists of a rule id and a reference to a node.
/// When inserted into a node `a` of the error graph, it means that we can
/// derive the configuration of `node` by applying the rule with id `rule_id` to
/// `a`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ErrorGraphEdge {
    /// Ids of the rules used to derive this edge
    rule_id: BTreeSet<u32>,
    /// Config of the successor node
    cfg: ACSTAConfig,
    /// Successor node which configuration can be derived by applying the rule
    /// with id `rule_id`
    node: NodeRef,
}

impl ErrorGraphEdge {
    /// Create a new [`ErrorGraphEdge`]
    ///
    /// Borrows `node` immutable during creation of the node
    pub fn new(rule: &CSRule, node: NodeRef) -> Self {
        let cfg = node.borrow().config().clone();

        Self {
            rule_id: BTreeSet::from([rule.id()]),
            node,
            cfg,
        }
    }

    /// Returns the configuration of the successor node of this edge
    pub fn get_successor_configuration(&self) -> &ACSTAConfig {
        &self.cfg
    }

    /// Get the id of the rule that this edge has been derived from
    pub fn get_ids_of_rules(&self) -> impl Iterator<Item = u32> {
        self.rule_id.iter().cloned()
    }

    /// Get the node this edge leads to
    pub fn node(&self) -> &NodeRef {
        &self.node
    }

    /// Insert a new edge into a collection of error graph edges
    pub fn insert_to_edge_collection(v: &mut Vec<ErrorGraphEdge>, e: ErrorGraphEdge) {
        let found = v.iter_mut().fold(false, |acc, x| {
            if !acc && x.get_successor_configuration() == e.get_successor_configuration() {
                x.rule_id.extend(e.rule_id.clone());
                return true;
            }
            acc
        });

        if !found {
            v.push(e);
        }
    }
}

#[cfg(test)]
mod new_mock {
    use std::collections::BTreeSet;

    use crate::error_graph::{NodeRef, edge::ErrorGraphEdge};

    impl ErrorGraphEdge {
        pub fn new_mock_with_id(r: u32, node: NodeRef) -> Self {
            let cfg = node.borrow().config().clone();

            Self {
                rule_id: BTreeSet::from([r]),
                node,
                cfg,
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use std::collections::BTreeSet;

    use crate::{
        acs_threshold_automaton::{
            ACSLocation, CSIntervalConstraint, CSRule, configuration::ACSTAConfig,
        },
        error_graph::{NodeRef, edge::ErrorGraphEdge, node::ErrorGraphNode},
    };

    #[test]
    fn test_error_graph_edge() {
        let node: NodeRef = ErrorGraphNode::new_mock(
            0,
            ACSTAConfig::new_mock_from_vecs(Vec::new(), Vec::new()),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .into();

        let rule = CSRule::new_mock(
            42,
            ACSLocation::new_mock(0),
            ACSLocation::new_mock(2),
            CSIntervalConstraint::False,
            Vec::new(),
        );

        let edge = ErrorGraphEdge::new(&rule, node.clone());

        assert_eq!(
            edge,
            ErrorGraphEdge {
                rule_id: BTreeSet::from([42]),
                node: node.clone(),
                cfg: node.borrow().config().clone(),
            }
        );

        assert_eq!(edge.get_ids_of_rules().collect::<Vec<_>>(), vec![42]);
        assert_eq!(edge.node(), &node);
        assert_eq!(
            edge.get_successor_configuration(),
            &ACSTAConfig::new_mock_from_vecs(Vec::new(), Vec::new())
        );
    }
}

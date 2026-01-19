//! This module contains the definition of a BDD context manager which
//! is used to create and manage BDD variables.

use std::collections::HashMap;
use std::fmt::Display;

use taco_bdd::{BDD, BDDManager, Bdd, BddManager};
use taco_interval_ta::IntervalThresholdAutomaton;
use taco_interval_ta::{IntervalTARule, interval::Interval};
use taco_threshold_automaton::ThresholdAutomaton;
use taco_threshold_automaton::expressions::{Location, Variable};

/// Manager for BDD variables for an underlying IntervalThresholdAutomaton
#[derive(Debug, Clone)]
pub struct BddVarManager {
    /// The BDD manager
    manager: BDDManager,
    /// BDD variables for each location
    loc_vars: HashMap<Location, BDD>,
    /// Location successor BDD variables
    loc_vars_primed: HashMap<Location, BDD>,
    /// BDD variables for each variable
    variable_vars: HashMap<Variable, Vec<BDD>>,
    /// Variable successor BDD variables
    variable_vars_primed: HashMap<Variable, Vec<BDD>>,
    /// Mapping for each variable from unprimed interval to the corresponding BDD
    shared_interval_to_bdd: HashMap<Variable, HashMap<Interval, BDD>>,
    /// Mapping for each variable from primed interval to the correspond BDD
    shared_primed_interval_to_bdd: HashMap<Variable, HashMap<Interval, BDD>>,
    /// BDD variables to represent the rule_id
    rule_vars: Vec<BDD>,
    /// Mapping from abstract rule to the corresponding BDD
    rule_to_bdd: HashMap<IntervalTARule, BDD>,
    /// All unprimed bdd variables for locations and shared variables
    unprimed_vars_vec: Vec<BDD>,
    /// All primed bdd variables for locations and shared variables
    primed_vars_vec: Vec<BDD>,
}

impl BddVarManager {
    /// creates a new BDDVarManager
    pub fn new(mgr: BDDManager, automaton: &IntervalThresholdAutomaton) -> Self {
        let mut bdd_mgr = BddVarManager {
            manager: mgr,
            loc_vars: HashMap::new(),
            loc_vars_primed: HashMap::new(),
            variable_vars: HashMap::new(),
            variable_vars_primed: HashMap::new(),
            shared_interval_to_bdd: HashMap::new(),
            shared_primed_interval_to_bdd: HashMap::new(),
            rule_vars: Vec::new(),
            rule_to_bdd: HashMap::new(),
            unprimed_vars_vec: Vec::new(),
            primed_vars_vec: Vec::new(),
        };
        bdd_mgr.initialize(automaton);
        bdd_mgr
    }

    /// initializes the bdd_var_manager
    ///
    /// 1. create unprimed and primed location vars
    /// 2. create unprimed and primed shared variable intervals
    /// 3. create bdd_variables to represent rules
    /// 4. create ordered vectors for all unprimed and primed bdd variables
    fn initialize(&mut self, aut: &IntervalThresholdAutomaton) {
        // 1. create unprimed and primed location vars
        self.initialize_loc_vars(aut);

        // 2. create unprimed and primed shared variable intervals
        self.initialize_shared_vars(aut);

        // 3. create bdd_variables to represent rules
        self.initialize_rule_vars(aut);

        //4. create ordered vectors for all unprimed and primed bdd variables
        self.create_unprimed_primed_vecs();
    }

    /// initializes all unprimed and primed bdd variables for locations
    fn initialize_loc_vars(&mut self, aut: &IntervalThresholdAutomaton) {
        let locations = aut.locations();
        for loc in locations {
            // create unprimed and primed bdd variables for each location
            self.new_location_var(loc);
            self.new_primed_location_var(loc);
        }
    }

    /// initializes all unprimed and primed bdd variables for shared variables
    fn initialize_shared_vars(&mut self, aut: &IntervalThresholdAutomaton) {
        for shared_var in aut.variables() {
            // check how many bdd variables are needed to represent all intervals binary
            // and create as many primed and unprimed bdd variables
            let num_intervals = aut.get_intervals(shared_var).len();
            for _ in 0..format!("{:b}", num_intervals - 1).len() {
                self.new_shared_var(shared_var);
                self.new_primed_shared_var(shared_var);
            }
            // encode each interval as a bdd
            for (index, interval) in aut.get_intervals(shared_var).iter().enumerate() {
                let bdd = self.encode_bitwise_bdd(
                    index as u32,
                    self.variable_vars
                        .get(shared_var)
                        .expect("error getting shared bdd variables"),
                );

                self.shared_interval_to_bdd
                    .entry(shared_var.clone())
                    .or_default()
                    .insert(interval.clone(), bdd.clone());

                let vars_shared_primed = self
                    .variable_vars_primed
                    .get(shared_var)
                    .expect("error getting shared bdd variables");
                let bdd = self.encode_bitwise_bdd(index as u32, vars_shared_primed);

                self.shared_primed_interval_to_bdd
                    .entry(shared_var.clone())
                    .or_default()
                    .insert(interval.clone(), bdd.clone());
            }
        }
    }

    // initializes all bdd variables for abstract rules
    fn initialize_rule_vars(&mut self, aut: &IntervalThresholdAutomaton) {
        // check how many bdd variables are needed to represent the maximum rule_id binary
        // and create as many bdd variables
        let num_rules = aut.rules().count();
        for _ in 0..num_rules.checked_ilog2().map_or(0, |n| n + 1) {
            self.new_rule_var();
        }
        // encode each rule_id as a bdd
        for (counter, rule) in aut.rules().enumerate() {
            let bdd = self.encode_bitwise_bdd(
                counter.try_into().expect("rule index exceeds u32::MAX"),
                &self.rule_vars,
            );
            self.rule_to_bdd.insert(rule.clone(), bdd.clone());
        }
    }

    /// get the BDD variable for a location
    pub fn get_location_var(&self, loc: &Location) -> Result<&BDD, BDDVarManagerError> {
        self.loc_vars
            .get(loc)
            .ok_or_else(|| BDDVarManagerError::LocationVarsNotDeclared(loc.clone()))
    }

    /// get the primed BDD variable for a location
    pub fn get_primed_location_var(&self, loc: &Location) -> Result<&BDD, BDDVarManagerError> {
        self.loc_vars_primed
            .get(loc)
            .ok_or_else(|| BDDVarManagerError::NoPrimedLocationVar(loc.clone()))
    }

    /// get the BDD variables for a shared variable
    pub fn get_shared_interval_bdd(
        &self,
        shared: &Variable,
        interval: &Interval,
    ) -> Result<&BDD, BDDVarManagerError> {
        self.shared_interval_to_bdd
            .get(shared)
            .ok_or_else(|| {
                BDDVarManagerError::NoSharedIntervalBdd(shared.clone(), Box::new(interval.clone()))
            })?
            .get(interval)
            .ok_or_else(|| {
                BDDVarManagerError::NoSharedIntervalBdd(shared.clone(), Box::new(interval.clone()))
            })
    }

    /// get the primed BDD variables for a shared variable
    pub fn get_primed_shared_interval_bdd(
        &self,
        shared: &Variable,
        interval: &Interval,
    ) -> Result<&BDD, BDDVarManagerError> {
        self.shared_primed_interval_to_bdd
            .get(shared)
            .ok_or_else(|| {
                BDDVarManagerError::NoPrimedSharedIntervalBdd(
                    shared.clone(),
                    Box::new(interval.clone()),
                )
            })?
            .get(interval)
            .ok_or_else(|| {
                BDDVarManagerError::NoPrimedSharedIntervalBdd(
                    shared.clone(),
                    Box::new(interval.clone()),
                )
            })
    }

    /// get the BDD for an abstract rule
    pub fn get_rule_bdd(&self, rule: &IntervalTARule) -> Result<&BDD, BDDVarManagerError> {
        self.rule_to_bdd
            .get(rule)
            .ok_or_else(|| BDDVarManagerError::NoAbstractRuleBdd(Box::new(rule.clone())))
    }

    /// get the constant true BDD
    pub fn get_bdd_true(&self) -> BDD {
        self.manager.get_bdd_true()
    }

    /// get the constant false BDD
    pub fn get_bdd_false(&self) -> BDD {
        self.manager.get_bdd_false()
    }

    /// creates and stores a new bdd variable to represent a given location
    fn new_location_var(&mut self, loc: &Location) {
        let loc_var = self.manager.new_var();
        self.loc_vars.insert(loc.clone(), loc_var.clone());
    }

    /// creates and stores a new primed bdd variable to represent a given location
    fn new_primed_location_var(&mut self, loc: &Location) {
        let primed_loc_var = self.manager.new_var();
        self.loc_vars_primed
            .insert(loc.clone(), primed_loc_var.clone());
    }

    /// creates and stores a new bdd variable to represent the interval of a shared variable
    fn new_shared_var(&mut self, shared: &Variable) {
        let shared_var = self.manager.new_var();
        self.variable_vars
            .entry(shared.clone())
            .or_default()
            .push(shared_var.clone());
    }

    /// creates and stores a new primed bdd variable to represent the interval of a shared variable
    fn new_primed_shared_var(&mut self, shared: &Variable) {
        let primed_shared_var = self.manager.new_var();
        self.variable_vars_primed
            .entry(shared.clone())
            .or_default()
            .push(primed_shared_var.clone());
    }

    /// creates and stores a new bdd variable to represent a rule
    fn new_rule_var(&mut self) {
        let rule_var = self.manager.new_var();
        self.rule_vars.push(rule_var.clone());
    }

    /// Given `index` and a vector of bdd variables,
    /// Returns the bitwise encoded bdd for `index` if enough bdd variables are provided
    fn encode_bitwise_bdd(&self, index: u32, bdd_vars: &[BDD]) -> BDD {
        let mut index_binary = index;
        let mut bitwise_bdd = self.manager.get_bdd_true();
        for bdd in bdd_vars.iter().rev() {
            if index_binary % 2 == 1 {
                bitwise_bdd = bitwise_bdd.and(bdd);
            } else {
                bitwise_bdd = bitwise_bdd.and(&bdd.not());
            }
            index_binary >>= 1;
        }
        bitwise_bdd
    }

    /// Constructs a constraint which checks that the bdd variables for an unprimed and primed shared variable are unchanged
    pub fn get_unchanged_interval_bdd(&self, shared: &Variable) -> Result<BDD, BDDVarManagerError> {
        let unprimed_vars = self
            .variable_vars
            .get(shared)
            .ok_or_else(|| BDDVarManagerError::NoUnprimedSharedVars(shared.clone()))?;

        let primed_vars = self
            .variable_vars_primed
            .get(shared)
            .ok_or_else(|| BDDVarManagerError::NoPrimedSharedVars(shared.clone()))?;

        Ok(unprimed_vars
            .iter()
            .zip(primed_vars.iter())
            .fold(self.get_bdd_true(), |acc, (unprimed_var, primed_var)| {
                acc.and(&(unprimed_var.equiv(primed_var)))
            }))
    }

    /// Creates an ordered vector for all unprimed and primed bdd variables
    fn create_unprimed_primed_vecs(&mut self) {
        // add all unprimed and primed bdd variables for locations
        for (loc, bdd) in self.loc_vars.iter() {
            self.unprimed_vars_vec.push(bdd.clone());
            let primed_bdd = self
                .loc_vars_primed
                .get(loc)
                .ok_or_else(|| BDDVarManagerError::NoPrimedLocationVar(loc.clone()))
                .expect("error getting primed location bdd");
            self.primed_vars_vec.push(primed_bdd.clone());
        }

        //add all unprimed and primed bdd variables for shared variables
        for (shared, bdd_vec) in self.variable_vars.iter() {
            self.unprimed_vars_vec.extend(bdd_vec.clone());

            let primed_bdd_vec = self
                .variable_vars_primed
                .get(shared)
                .ok_or_else(|| BDDVarManagerError::NoPrimedSharedVars(shared.clone()))
                .expect("error getting primed shared bdd variable");

            self.primed_vars_vec.extend(primed_bdd_vec.clone());
        }
    }

    /// Swaps all unprimed and primed bdd variables for `cur`
    pub fn swap_unprimed_primed_bdd_vars(&self, cur: &BDD) -> BDD {
        cur.swap(&self.unprimed_vars_vec, &self.primed_vars_vec)
    }

    /// abstracts all bdd variables for unprimed locations and unprimed shared variables for a given bdd
    pub fn exists_unprimed(&self, cur: &BDD) -> BDD {
        // abstract unprimed locations and unprimed shared variables
        let vec_unprimed_vars = self
            .loc_vars
            .values()
            .chain(self.variable_vars.values().flatten());

        cur.exists(vec_unprimed_vars)
    }

    /// abstracts all primed bdd variables for primed locations and primed shared variables for a given bdd `cur`
    pub fn exists_primed(&self, cur: &BDD) -> BDD {
        // abstract primed locations and primed shared variables
        let vec_primed_vars = self
            .loc_vars_primed
            .values()
            .chain(self.variable_vars_primed.values().flatten());

        cur.exists(vec_primed_vars)
    }

    /// abstracts all bdd variables for rule_ids for a given bdd `cur`
    pub fn exists_rule_vars(&self, cur: &BDD) -> BDD {
        cur.exists(&self.rule_vars)
    }
}

/// Custom Error type to indicate an error
/// when creating a new bdd variable or trying to access an uninitialized one
#[derive(Debug, Clone)]
pub enum BDDVarManagerError {
    /// Error indicating that there exists no bdd variable for this location
    LocationVarsNotDeclared(Location),
    /// Error indicating that there exists no primed bdd variables for this location
    NoPrimedLocationVar(Location),
    /// Error indicating that there exists no unprimed bdd variable for this shared variable
    NoUnprimedSharedVars(Variable),
    /// Error indicating that there exists no primed bdd variable for this shared variable
    NoPrimedSharedVars(Variable),
    /// Error indicating that there exist no bdd for this shared variable and this interval
    NoSharedIntervalBdd(Variable, Box<Interval>),
    /// Error indicating that there exist no primed bdd for this shared variable and this interval
    NoPrimedSharedIntervalBdd(Variable, Box<Interval>),
    /// Error indicating that there exist no bdd for this abstract rule
    NoAbstractRuleBdd(Box<IntervalTARule>),
}

impl std::error::Error for BDDVarManagerError {}

impl Display for BDDVarManagerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BDDVarManagerError::LocationVarsNotDeclared(loc) => {
                write!(f, "There exists no bdd variable for location {loc}")
            }
            BDDVarManagerError::NoPrimedLocationVar(loc) => {
                write!(f, "There exists no primed bdd variable for location {loc}")
            }
            BDDVarManagerError::NoUnprimedSharedVars(shared) => write!(
                f,
                "There exists no unprimed bdd variables for shared variable {shared}"
            ),
            BDDVarManagerError::NoPrimedSharedVars(shared) => write!(
                f,
                "There exists no primed bdd variables for shared variable {shared}"
            ),
            BDDVarManagerError::NoSharedIntervalBdd(shared, interval) => write!(
                f,
                "There exists no bdd for shared variable {shared} and interval {interval}"
            ),
            BDDVarManagerError::NoPrimedSharedIntervalBdd(shared, interval) => write!(
                f,
                "There exists no primed bdd for shared variable {shared} and interval {interval}"
            ),
            BDDVarManagerError::NoAbstractRuleBdd(rule) => {
                write!(f, "There exists no bdd for abstract rule {rule}")
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::BddVarManager;
    use crate::zcs::bdd_var_manager::BDDVarManagerError;
    use taco_bdd::BDD;
    use taco_bdd::BDDManager;
    use taco_bdd::Bdd;
    use taco_interval_ta::interval::{Interval, IntervalBoundary};
    use taco_interval_ta::{IntervalConstraint, IntervalTARule};

    use taco_threshold_automaton::expressions::{
        ComparisonOp, IntegerExpression, Location, Parameter, Variable,
    };
    use taco_threshold_automaton::general_threshold_automaton::builder::RuleBuilder;

    use taco_interval_ta::IntervalThresholdAutomaton;
    use taco_interval_ta::builder::IntervalTABuilder;
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::BooleanVarConstraint;
    use taco_threshold_automaton::RuleDefinition;
    use taco_threshold_automaton::ThresholdAutomaton;
    use taco_threshold_automaton::expressions::fraction::Fraction;
    use taco_threshold_automaton::general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder;
    use taco_threshold_automaton::lia_threshold_automaton::LIAThresholdAutomaton;
    use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::WeightedSum;

    const LOCATION_L0: &str = "l0";
    const LOCATION_L1: &str = "l1";
    const VARIABLE_X: &str = "x";
    const VARIABLE_Y: &str = "y";

    /// this function is used to instantiate a BddVarManager for the following test cases
    /// for each location { l0, l1 }, a primed and unprimed bdd variable is created
    /// for shared variable x, one bdd variable is created (primed and unprimed each)
    /// for shared variable y, two bdd variables are created (primed and unprimed each)
    /// for rule_ids, two bdd variables are created
    /// shared variable x has two intervals I_1 and I_2
    /// shared variable y has four intervals I_1, I_2, I_3 and I_4
    /// there are 4 abstract rules
    fn get_test_aut() -> IntervalThresholdAutomaton {
        let var_x = Variable::new(VARIABLE_X);
        let var_y = Variable::new(VARIABLE_Y);

        let ta = GeneralThresholdAutomatonBuilder::new("test_ta")
            .with_variables(vec![var_x.clone(), var_y.clone()])
            .unwrap()
            .with_locations([Location::new(LOCATION_L0), Location::new(LOCATION_L1)])
            .unwrap()
            .with_parameter(Parameter::new("n"))
            .unwrap()
            .initialize()
            .with_rules(vec![
                RuleBuilder::new(0, Location::new(LOCATION_L0), Location::new(LOCATION_L0))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var_x.clone())),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(0)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var_y.clone())),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(0)),
                        ),
                    )
                    .build(),
                RuleBuilder::new(1, Location::new(LOCATION_L0), Location::new(LOCATION_L1))
                    .with_guard(
                        BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var_x.clone())),
                            ComparisonOp::Geq,
                            Box::new(IntegerExpression::Const(1)),
                        ) & BooleanVarConstraint::ComparisonExpression(
                            Box::new(IntegerExpression::Atom(var_y.clone())),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1)),
                        ),
                    )
                    .build(),
                RuleBuilder::new(2, Location::new(LOCATION_L1), Location::new(LOCATION_L0))
                    .with_guard(BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var_y.clone())),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(2)),
                    ))
                    .build(),
                RuleBuilder::new(3, Location::new(LOCATION_L1), Location::new(LOCATION_L1))
                    .with_guard(BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(var_y.clone())),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(3)),
                    ))
                    .build(),
            ])
            .unwrap()
            .build();

        let lia_ta = LIAThresholdAutomaton::try_from(ta).unwrap();

        let mut interval_tas = IntervalTABuilder::new(lia_ta, SMTSolverBuilder::default(), vec![])
            .build()
            .expect("Failed creating IntervalTA");
        let ita = interval_tas.next().unwrap();

        assert!(
            interval_tas.next().is_none(),
            "There should be only one interval ta in this test"
        );

        ita
    }

    /// this function creates the following bdd with bdd variables created in get_test_mgr()
    /// the bdd is used for test purposes
    /// taco_bdd: (l_0 & (l_1' | !(x & r_0))) | (!l_0' & (r_1 | y_1'))
    fn get_test_bdd(mgr: &BddVarManager) -> BDD {
        let l_0 = mgr.get_location_var(&Location::new("l0")).unwrap();
        let l_0_prime = mgr.get_primed_location_var(&Location::new("l0")).unwrap();
        let l_1_prime = mgr.get_primed_location_var(&Location::new("l1")).unwrap();

        // x == I_2
        let i_x_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let x = mgr
            .get_shared_interval_bdd(&Variable::new("x"), &i_x_2)
            .unwrap();

        // y_1' = I_3' | I_4'
        let interval_3 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(2, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(3, 1, false)),
            true,
        );
        let interval_4 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(3, 1, false)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let y_1_prime = mgr
            .get_primed_shared_interval_bdd(&Variable::new("y"), &interval_3)
            .unwrap()
            .or(mgr
                .get_primed_shared_interval_bdd(&Variable::new("y"), &interval_4)
                .unwrap());

        let ata = get_test_aut();
        // r_0 = rule_1 | rule_3
        let rule_1 = ata.rules().find(|r| r.id() == 1).unwrap();
        let rule_2 = ata.rules().find(|r| r.id() == 2).unwrap();
        let rule_3 = ata.rules().find(|r| r.id() == 3).unwrap();

        let r_0 = mgr
            .get_rule_bdd(rule_1)
            .unwrap()
            .or(mgr.get_rule_bdd(rule_3).unwrap());

        // r_1 = rule_2 | rule_3
        let r_1 = mgr
            .get_rule_bdd(rule_2)
            .unwrap()
            .or(mgr.get_rule_bdd(rule_3).unwrap());

        let lhs = l_0.and(&(l_1_prime.or(&((x.and(&r_0)).not()))));
        let rhs = (l_0_prime.not()).and(&(r_1.or(&y_1_prime)));
        lhs.or(&rhs)
    }

    #[test]
    fn test_get_loc_var() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        assert!(
            mgr.get_location_var(&Location::new("l0"))
                .unwrap()
                .satisfiable()
        );
        assert!(
            !mgr.get_location_var(&Location::new("l0"))
                .unwrap()
                .eq(&mgr.get_bdd_true())
        );
        assert!(
            mgr.get_primed_location_var(&Location::new("l0"))
                .unwrap()
                .satisfiable()
        );
        assert!(
            !mgr.get_primed_location_var(&Location::new("l0"))
                .unwrap()
                .eq(&mgr.get_bdd_true())
        );
        assert!(
            !mgr.get_location_var(&Location::new("l0"))
                .unwrap()
                .eq(mgr.get_location_var(&Location::new("l1")).unwrap())
        );
        assert!(
            !mgr.get_location_var(&Location::new("l0"))
                .unwrap()
                .eq(mgr.get_primed_location_var(&Location::new("l0")).unwrap())
        );
    }

    #[test]
    fn test_error_get_location_var() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let error = mgr.get_location_var(&Location::new("l2"));

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::LocationVarsNotDeclared(_)
        ));
    }

    #[test]
    fn test_error_get_primed_location_var() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let error = mgr.get_primed_location_var(&Location::new("l2"));

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoPrimedLocationVar(_)
        ));
    }

    #[test]
    fn test_shared_interval_bdd() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let i_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(0, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            true,
        );
        let i_x_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let i_y_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(2, 1, false)),
            true,
        );

        assert!(
            !mgr.get_shared_interval_bdd(&Variable::new("x"), &i_1)
                .unwrap()
                .eq(&mgr.get_bdd_true())
        );
        assert!(
            !mgr.get_shared_interval_bdd(&Variable::new("x"), &i_1)
                .unwrap()
                .eq(&mgr.get_bdd_false())
        );
        assert!(
            !mgr.get_shared_interval_bdd(&Variable::new("x"), &i_x_2)
                .unwrap()
                .eq(mgr
                    .get_primed_shared_interval_bdd(&Variable::new("x"), &i_x_2)
                    .unwrap())
        );
        assert!(
            !mgr.get_shared_interval_bdd(&Variable::new("y"), &i_y_2)
                .unwrap()
                .eq(mgr
                    .get_shared_interval_bdd(&Variable::new("y"), &i_1)
                    .unwrap())
        );
    }

    #[test]
    fn test_error_get_shared_interval_bdd_unknown_var() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let i_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(0, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            true,
        );

        let error = mgr.get_shared_interval_bdd(&Variable::new("z"), &i_1);

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoSharedIntervalBdd(_, _)
        ));
    }

    #[test]
    fn test_error_get_shared_interval_bdd_unknown_interval() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let interval_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(2, 1, false)),
            true,
        );

        let error = mgr.get_shared_interval_bdd(&Variable::new("x"), &interval_2);

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoSharedIntervalBdd(_, _)
        ));
    }

    #[test]
    fn test_error_get_primed_shared_interval_bdd_unknown_var() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let i_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(0, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            true,
        );

        let error = mgr.get_primed_shared_interval_bdd(&Variable::new("z"), &i_1);

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoPrimedSharedIntervalBdd(_, _)
        ));
    }

    #[test]
    fn test_error_get_primed_shared_interval_bdd_unknown_interval() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let i_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(2, 1, false)),
            true,
        );

        let error = mgr.get_primed_shared_interval_bdd(&Variable::new("x"), &i_2);

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoPrimedSharedIntervalBdd(_, _)
        ));
    }

    #[test]
    fn test_get_rule_bdd() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);
        let rule_0 = ata.rules().find(|r| r.id() == 0).unwrap();
        let rule_1 = ata.rules().find(|r| r.id() == 1).unwrap();
        let rule_2 = ata.rules().find(|r| r.id() == 2).unwrap();
        let rule_3 = ata.rules().find(|r| r.id() == 3).unwrap();

        assert!(mgr.get_rule_bdd(rule_0).is_ok());
        assert!(mgr.get_rule_bdd(rule_1).is_ok());
        assert!(mgr.get_rule_bdd(rule_2).is_ok());
        assert!(mgr.get_rule_bdd(rule_3).is_ok());
        assert!(mgr.get_rule_bdd(rule_0).unwrap().satisfiable());
        assert!(!mgr.get_rule_bdd(rule_0).unwrap().eq(&mgr.get_bdd_true()));
        assert!(
            !mgr.get_rule_bdd(rule_0)
                .unwrap()
                .eq(mgr.get_rule_bdd(rule_1).unwrap())
        );
    }

    #[test]
    fn test_error_get_rule_bdd() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let rule = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            Vec::new(),
        );

        let error = mgr.get_rule_bdd(&rule);

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoAbstractRuleBdd(_)
        ));
    }

    #[test]
    fn test_encode_bitwise_bdd() {
        let ata = get_test_aut();
        let mut mgr = BddVarManager::new(BDDManager::default(), &ata);

        mgr.new_shared_var(&Variable::new("z"));
        mgr.new_shared_var(&Variable::new("z"));
        let vec_variables = mgr.variable_vars.get(&Variable::new("z")).unwrap();
        let res = mgr.encode_bitwise_bdd(1, vec_variables);
        assert!(res.eq(&(vec_variables[0].not().and(&vec_variables[1]))));
    }

    #[test]
    fn test_get_unchanged_interval_bdd() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let unprimed_vars = mgr.variable_vars.get(&Variable::new("y")).unwrap();
        let primed_vars = mgr.variable_vars_primed.get(&Variable::new("y")).unwrap();

        let correct_bdd = unprimed_vars[0]
            .clone()
            .equiv(&primed_vars[0])
            .and(&primed_vars[1].equiv(&unprimed_vars[1]));
        let res = mgr.get_unchanged_interval_bdd(&Variable::new("y"));
        assert!(res.is_ok());
        assert!(res.unwrap().eq(&correct_bdd));
    }

    #[test]
    fn test_error_get_unchanged_interval_bdd_no_unprimed_vars() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let error = mgr.get_unchanged_interval_bdd(&Variable::new("z"));

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoUnprimedSharedVars(_)
        ));
    }

    #[test]
    fn test_error_get_unchanged_interval_bdd_no_primed_vars() {
        let ata = get_test_aut();
        let mut mgr = BddVarManager::new(BDDManager::default(), &ata);

        mgr.new_shared_var(&Variable::new("z"));
        let error = mgr.get_unchanged_interval_bdd(&Variable::new("z"));

        assert!(error.is_err());

        assert!(matches!(
            error.clone().unwrap_err(),
            BDDVarManagerError::NoPrimedSharedVars(_)
        ));
    }

    #[test]
    fn test_create_unprimed_primed_vecs() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        assert_eq!(mgr.unprimed_vars_vec.len(), mgr.primed_vars_vec.len());
    }

    #[test]
    fn test_swap_unprimed_primed_bdd() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);

        let l_0 = mgr.get_location_var(&Location::new("l0")).unwrap();
        let l_0_prime = mgr.get_primed_location_var(&Location::new("l0")).unwrap();
        // r_0 = rule_1 | rule_3
        let rule_1 = ata.rules().find(|r| r.id() == 1).unwrap();
        let rule_3 = ata.rules().find(|r| r.id() == 3).unwrap();

        let r_0 = mgr
            .get_rule_bdd(rule_1)
            .unwrap()
            .or(mgr.get_rule_bdd(rule_3).unwrap());

        let mut res = mgr.swap_unprimed_primed_bdd_vars(&l_0.and(&r_0));

        assert_eq!(res, l_0_prime.and(&r_0));

        res = mgr.swap_unprimed_primed_bdd_vars(&l_0.and(&r_0.and(&l_0_prime.not())));
        assert_eq!(res, l_0_prime.and(&r_0.and(&l_0.not())));

        let interval_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(0, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            true,
        );

        let i_0 = mgr
            .get_shared_interval_bdd(&Variable::new("x"), &interval_1.clone())
            .unwrap();
        let i_0_prime = mgr
            .get_primed_shared_interval_bdd(&Variable::new("x"), &interval_1.clone())
            .unwrap();

        res = mgr.swap_unprimed_primed_bdd_vars(&i_0.and(&i_0_prime.not()));
        assert!(res.eq(&i_0_prime.and(&i_0.not())));
    }

    #[test]
    fn test_exists_unprimed() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);
        let l_0 = mgr.get_location_var(&Location::new("l0")).unwrap();
        let l_0_prime = mgr.get_primed_location_var(&Location::new("l0")).unwrap();

        // r_1 = rule_2 | rule_3
        let rule_2 = ata.rules().find(|r| r.id() == 2).unwrap();
        let rule_3 = ata.rules().find(|r| r.id() == 3).unwrap();

        let r_1 = mgr
            .get_rule_bdd(rule_2)
            .unwrap()
            .or(mgr.get_rule_bdd(rule_3).unwrap());

        // y_1' = I_2' | I_3'
        let interval_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(2, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(3, 1, false)),
            true,
        );
        let interval_3 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(3, 1, false)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let y_1_prime = mgr
            .get_primed_shared_interval_bdd(&Variable::new("y"), &interval_2)
            .unwrap()
            .or(mgr
                .get_primed_shared_interval_bdd(&Variable::new("y"), &interval_3)
                .unwrap());

        // test_bdd & !l_0
        let test_bdd = get_test_bdd(&mgr).and(&l_0.not());
        // (r_1 | y_1') & !l_0
        let correct_bdd = l_0_prime.not().and(&(r_1.or(&y_1_prime)));
        let abstract_bdd = mgr.exists_unprimed(&test_bdd);
        assert!(correct_bdd.eq(&abstract_bdd));
    }

    #[test]
    fn test_exists_primed() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);
        let l_0 = mgr.get_location_var(&Location::new("l0")).unwrap();
        let l_0_prime = mgr.get_primed_location_var(&Location::new("l0")).unwrap();
        let l_1_prime = mgr.get_primed_location_var(&Location::new("l1")).unwrap();

        // r_0 = rule_1 | rule_3
        let rule_1 = ata.rules().find(|r| r.id() == 1).unwrap();
        let rule_3 = ata.rules().find(|r| r.id() == 3).unwrap();

        let r_0 = mgr
            .get_rule_bdd(rule_1)
            .unwrap()
            .or(mgr.get_rule_bdd(rule_3).unwrap());

        // x = I_2
        let interval_2 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            false,
            IntervalBoundary::Infty,
            true,
        );
        let x = mgr
            .get_shared_interval_bdd(&Variable::new("x"), &interval_2)
            .unwrap();

        // test_bdd & l_0' & !l_1'
        let test_bdd = get_test_bdd(&mgr).and(l_0_prime).and(&l_1_prime.not());
        // (l_0 & !(x & r_0))
        let correct_bdd = l_0.and(&(x.and(&r_0)).not());
        let abstract_bdd = mgr.exists_primed(&test_bdd);
        assert!(correct_bdd.eq(&abstract_bdd));
    }

    #[test]
    fn test_exists_rule_vars() {
        let ata = get_test_aut();
        let mgr = BddVarManager::new(BDDManager::default(), &ata);
        let l_0 = mgr.get_location_var(&Location::new("l0")).unwrap();
        let l_0_prime = mgr.get_primed_location_var(&Location::new("l0")).unwrap();
        // l_0 | !l_0'
        let correct_bdd = l_0.or(&l_0_prime.not());
        let abstract_bdd = mgr.exists_rule_vars(&get_test_bdd(&mgr));
        assert!(correct_bdd.eq(&abstract_bdd));
    }

    #[test]
    fn test_display_error() {
        let ata = get_test_aut();
        let mut mgr = BddVarManager::new(BDDManager::default(), &ata);

        let error_loc = mgr.get_location_var(&Location::new("l2"));
        assert!(error_loc.is_err());
        assert_eq!(
            "There exists no bdd variable for location l2".to_owned(),
            format!("{}", error_loc.unwrap_err().to_owned())
        );

        let error_primed_loc = mgr.get_primed_location_var(&Location::new("l2"));
        assert!(error_primed_loc.is_err());
        assert_eq!(
            "There exists no primed bdd variable for location l2".to_owned(),
            format!("{}", error_primed_loc.unwrap_err().to_owned())
        );

        let i_1 = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(0, 1, false)),
            false,
            IntervalBoundary::new_bound(WeightedSum::new_empty(), Fraction::new(1, 1, false)),
            true,
        );
        let error_shared = mgr.get_shared_interval_bdd(&Variable::new("z"), &i_1);
        assert!(error_shared.is_err());
        assert_eq!(
            "There exists no bdd for shared variable z and interval [0, 1[".to_owned(),
            format!("{}", error_shared.unwrap_err().to_owned())
        );

        let error_primed_shared = mgr.get_primed_shared_interval_bdd(&Variable::new("z"), &i_1);
        assert!(error_primed_shared.is_err());
        assert_eq!(
            "There exists no primed bdd for shared variable z and interval [0, 1[".to_owned(),
            format!("{}", error_primed_shared.unwrap_err().to_owned())
        );

        let rule = IntervalTARule::new(
            0,
            Location::new("l0"),
            Location::new("l1"),
            IntervalConstraint::True,
            Vec::new(),
        );
        let error_rule = mgr.get_rule_bdd(&rule);
        assert!(error_rule.is_err());
        assert_eq!(
            "There exists no bdd for abstract rule 0: l0 -> l1\n    when ( true )\n    do {  }"
                .to_owned(),
            format!("{}", error_rule.unwrap_err().to_owned())
        );

        let error_shared = mgr.get_unchanged_interval_bdd(&Variable::new("z"));
        assert!(error_shared.is_err());
        assert_eq!(
            "There exists no unprimed bdd variables for shared variable z".to_owned(),
            format!("{}", error_shared.unwrap_err().to_owned())
        );

        mgr.variable_vars.insert(Variable::new("z"), vec![]);
        let error_primed_shared = mgr.get_unchanged_interval_bdd(&Variable::new("z"));
        assert!(error_primed_shared.is_err());
        assert_eq!(
            "There exists no primed bdd variables for shared variable z".to_owned(),
            format!("{}", error_primed_shared.unwrap_err().to_owned())
        );
    }
}

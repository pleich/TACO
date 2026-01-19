//! TLA+ Parser module
//!
//! This module implements the parse for TLA+ specification files. You can find
//! more information on the supported syntax under `./docs/tla-to-ta.md`

use std::collections::HashMap;

use taco_display_utils::join_iterator;

use log::{debug, warn};
use pest::{
    Parser, Span,
    iterators::{Pair, Pairs},
};
use pest_derive::Parser;
use taco_model_checker::eltl::ELTLSpecificationBuilder;

use anyhow::{Context, Error, anyhow};
use taco_threshold_automaton::{
    ModifiableThresholdAutomaton, RuleDefinition, ThresholdAutomaton,
    expressions::{
        Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp,
        IsDeclared, Location, Parameter, Variable,
    },
    general_threshold_automaton::{
        self, GeneralThresholdAutomaton,
        builder::{
            GeneralThresholdAutomatonBuilder, InitializedGeneralThresholdAutomatonBuilder,
            RuleBuilder,
        },
    },
};

use crate::{
    ParseTA, ParseTAWithLTL,
    tla::integer_exprs::{
        parse_int_boolean_expr, parse_integer_const, parse_integer_update_expr,
        parse_ltl_specification,
    },
};

mod integer_exprs;

/// Constant for representing set of processes
const PROC_SET: &str = "Processes";
/// Constant for specifying the number of correct processes
const N_CORR_PROC: &str = "NbOfCorrProc";
/// Variable that is used to specify the set of locations
const LOCATIONS_SET: &str = "ProcessesLocations";

// Location of the grammar file and generation of parser
#[allow(missing_docs)]
#[derive(Parser)]
#[grammar = "./tla_format.pest"]
struct PestTLAParser;

impl ParseTA for TLAParser {
    fn parse_ta(&self, input: &str) -> Result<GeneralThresholdAutomaton, Error> {
        let (ta, _, _) = self.parse_ta_and_return_ltl_pairs(input)?;
        Ok(ta)
    }
}

impl ParseTAWithLTL for TLAParser {
    fn parse_ta_and_spec(
        &self,
        input: &str,
    ) -> Result<
        (
            GeneralThresholdAutomaton,
            taco_model_checker::eltl::ELTLSpecification,
        ),
        Error,
    > {
        let (ta, pairs, ctx) = self.parse_ta_and_return_ltl_pairs(input)?;

        let ltl_spec = self.parse_specification_and_add_expressions(
            pairs,
            ELTLSpecificationBuilder::new(&ta),
            ctx,
        )?;
        let ltl_spec = ltl_spec.build();

        Ok((ta, ltl_spec))
    }
}

/// Helper context for storing information such as declared integer macros
/// during parsing
struct TLAParsingContext<'a> {
    /// Integer expression that defines relation of the number of correct
    /// processes to the other parameters of a threshold automaton
    param_to_corr_procs: Option<IntegerExpression<Location>>,
    /// Integers macros that have already been declared
    int_macro: HashMap<String, Pair<'a, Rule>>,
    /// Stores whether a `Spec` declaration has already been parsed
    spec_declaration_parsed: bool,
    /// Stores which rule ids appear inside the `Next` declaration
    rule_ids_in_next: Vec<u32>,
}
impl TLAParsingContext<'_> {
    pub fn new() -> Self {
        TLAParsingContext {
            param_to_corr_procs: None,
            int_macro: HashMap::new(),
            spec_declaration_parsed: false,
            rule_ids_in_next: Vec::new(),
        }
    }
}

/// Parser for supported subset of TLA+
///
/// This parser is designed to parse TLA+ specifications that fall into the
/// translatable fragment
pub struct TLAParser {}

impl Default for TLAParser {
    fn default() -> Self {
        Self::new()
    }
}

impl TLAParser {
    /// Create a new parser for TLA specifications
    pub fn new() -> Self {
        TLAParser {}
    }

    /// Parse specification list into ltl expressions
    fn parse_specification_and_add_expressions<'a>(
        &self,
        pair: Vec<Pair<'a, Rule>>,
        mut builder: ELTLSpecificationBuilder<'a, GeneralThresholdAutomaton>,
        ctx: TLAParsingContext,
    ) -> Result<ELTLSpecificationBuilder<'a, GeneralThresholdAutomaton>, anyhow::Error> {
        let pairs = pair.into_iter();

        let expressions = pairs
            .map(|spec| parse_ltl_specification(spec, &builder, &ctx))
            .collect::<Result<Vec<_>, Error>>()
            .with_context(|| "Failed to parse specifications: ")?;

        builder
            .add_expressions(expressions)
            .with_context(|| "Specification failed validation: ")?;
        Ok(builder)
    }

    fn parse_ta_and_return_ltl_pairs<'a>(
        &self,
        input: &'a str,
    ) -> Result<
        (
            GeneralThresholdAutomaton,
            Vec<Pair<'a, Rule>>,
            TLAParsingContext<'a>,
        ),
        Error,
    > {
        let mut ctx = TLAParsingContext::new();

        let mut pairs = PestTLAParser::parse(Rule::tla_definition, input)?;

        let mut pairs = pairs
            .next()
            .expect("Missing: variable declaration")
            .into_inner();
        let mut pair = pairs.next().expect("Missing: constant declaration");

        pair = Self::validate_module_imports(&mut pairs, pair);

        let builder = GeneralThresholdAutomatonBuilder::new("tla_ta");

        let (mut pair, builder) = Self::parse_constant_declaration(&mut pairs, pair, builder)?;

        // RC conditions can only be parsed once parameters, locations and variables have been declared
        let mut assume_to_parse_later = Vec::new();
        while pair.as_rule() == Rule::assume_declaration {
            assume_to_parse_later.push(pair);
            pair = pairs.next().expect("Missing: constant declaration");
        }

        let (pair, builder) = Self::parse_variable_declaration(&mut pairs, pair, builder)?;

        let (pair, builder) = Self::parse_type_ok(&mut pairs, pair, builder)?;

        let mut builder = builder;
        for rc in assume_to_parse_later {
            builder = Self::parse_assume_declaration(rc, builder, &mut ctx)?;
        }

        if ctx.param_to_corr_procs.is_none() {
            return Err(anyhow!(
                "Error after parsing all assumptions ('ASSSUME' statements): \
Missing constraint on the number of correct processes. You need to specify the \
relation of the number of correct processes '{N_CORR_PROC}' to the other \
parameters (example: '{N_CORR_PROC} = N - F')."
            ));
        }

        let (pair, builder) =
            Self::parse_initial_constraint_declaration(&mut pairs, pair, builder, &mut ctx)?;
        if pair.is_none() {
            warn!("TLA file does not declare rules");
            return Ok((builder.build(), Vec::new(), ctx));
        }

        let pair = Self::parse_int_macro_declarations(&mut pairs, Some(pair.unwrap()), &mut ctx);
        if pair.is_none() {
            warn!("TLA file does not declare rules");
            return Ok((builder.build(), Vec::new(), ctx));
        }

        let (pair, builder) =
            Self::parse_rule_declarations(&mut pairs, pair.unwrap(), builder, &mut ctx)?;

        let pair = Self::parse_next_declaration(&mut pairs, pair, &mut ctx)?;

        let pair = Self::validate_spec_declaration(&mut pairs, pair, &mut ctx, &builder)?;

        let mut ltl_pairs = Vec::new();

        let mut pair = pair;
        while pair.is_some() {
            let inner_pair = pair.unwrap();

            if inner_pair.as_rule() != Rule::int_macro_declaration
                && inner_pair.as_rule() != Rule::ltl_spec_declaration
            {
                pair = Some(inner_pair);
                break;
            }

            if inner_pair.as_rule() == Rule::int_macro_declaration {
                pair = Self::parse_int_macro_declarations(&mut pairs, Some(inner_pair), &mut ctx);
                continue;
            }

            ltl_pairs.push(inner_pair);
            pair = pairs.next();
        }

        let pair = Self::parse_next_declaration(&mut pairs, pair, &mut ctx)?;

        let pair = Self::validate_spec_declaration(&mut pairs, pair, &mut ctx, &builder)?;

        debug_assert!(
            pair.unwrap().as_rule() == Rule::EOI,
            "Expected no more tokens!"
        );

        if ctx.rule_ids_in_next.is_empty() {
            warn!(
                "TLA file does not declare 'Next' or the 'Next' declaration \
does not specify any rules. This will break compatibility with TLC. Using all \
declared rules!"
            );
        }

        let mut ta = builder.build();

        let rules_not_in_next = ta
            .rules()
            .filter(|r| !ctx.rule_ids_in_next.contains(&r.id()))
            .cloned()
            .collect::<Vec<_>>();
        if !rules_not_in_next.is_empty() {
            warn!(
                "The next constraint excludes some rules from the threshold \
automaton. The following rules will be not appear in the automaton: {}",
                join_iterator(
                    rules_not_in_next
                        .iter()
                        .map(|r| format!("'Rule{}'", r.id())),
                    ", "
                )
            );
            ta.retain_rules(|r| !rules_not_in_next.contains(r));
        }

        Ok((ta, ltl_pairs, ctx))
    }

    /// Validate the imports appearing in the TLA file
    ///
    /// This function will not fail, it will only produce warnings on TLC
    /// compatibility
    fn validate_module_imports<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
    ) -> Pair<'a, Rule> {
        if pair.as_rule() != Rule::module_declaration {
            warn!(
                "No module imports found. To maintain compatibility with TLC, \
at least 'Integers' and 'FiniteSets' should be imported (use \
'EXTENDS Integers, FiniteSets' at the beginning of the file)."
            );
            return pair;
        }

        let mut inner_pairs = pair.into_inner();
        let ident_list = inner_pairs
            .next()
            .expect("Expected identifier list in EXTENDS");

        let module_identifiers: Vec<String> = parse_identifier_list_to_t(ident_list);
        debug!(
            "TLA file imports modules: {}",
            join_iterator(module_identifiers.iter(), ", ")
        );

        if !module_identifiers.contains(&"Integers".to_string()) {
            warn!(
                "Module import 'Integers' not found. This will break \
compatibility with TLC."
            );
        }

        if !module_identifiers.contains(&"FiniteSets".to_string()) {
            warn!(
                "Module  import 'FiniteSet' not found. This will break \
compatibility with TLC."
            );
        }

        pairs.next().expect("Missing: constant declaration")
    }

    /// Parses all constant declarations
    ///
    /// This block will parse all consecutive `constant_declaration`s pairs.
    /// Every such block is `CONSTANT` declaration and declares the parameters
    /// of a threshold automaton.
    /// Additionally, the constants `NbOfCorrProcesses`  and `Processes` should
    /// be declared.
    fn parse_constant_declaration<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: GeneralThresholdAutomatonBuilder,
    ) -> Result<(Pair<'a, Rule>, GeneralThresholdAutomatonBuilder), anyhow::Error> {
        debug_assert!(
            pair.as_rule() == Rule::constant_declaration,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str()
        );

        let mut found_params = Vec::new();
        let mut pair = pair;
        while pair.as_rule() == Rule::constant_declaration {
            let mut inner_pairs = pair.into_inner();
            let inner_pair = inner_pairs.next().unwrap();

            debug_assert!(inner_pairs.next().is_none());

            let params: Vec<Parameter> = parse_identifier_list_to_t(inner_pair);
            found_params.extend(params);

            pair = pairs.next().expect("Missing: variable declaration");
        }

        if !found_params.contains(&Parameter::new(PROC_SET)) {
            return Err(anyhow!(
                "Missing special constant '{PROC_SET}': No declaration for\
constant '{PROC_SET}' which represents the set of processes was found. Please \
add a declaration for constant '{PROC_SET}'."
            ));
        }

        if !found_params.contains(&Parameter::new(N_CORR_PROC)) {
            return Err(anyhow!(
                "Missing special constant '{N_CORR_PROC}': No declaration for\
constant '{N_CORR_PROC}' which represents the number of processes executing \
correctly was found. Please add a declaration for constant '{N_CORR_PROC}'."
            ));
        }
        debug!(
            "TLA file declares constants: {}",
            join_iterator(found_params.iter(), ", ")
        );

        // remove the special parameters before adding to the threshold automaton
        found_params
            .retain(|p| p != &Parameter::new(PROC_SET) && p != &Parameter::new(N_CORR_PROC));

        let builder = builder.with_parameters(found_params).with_context(|| {
            "Error while parsing 'CONSTANT' / 'CONSTANTS' declaration, i.e., \
parameters for the threshold automaton: "
        })?;

        Ok((pair, builder))
    }

    /// Parse and validate an `ASSUME` block, i.e. a resilience condition
    ///
    /// This function parses one `ASSUME` definition, but there can be
    /// potentially multiple ones
    fn parse_assume_declaration<'a>(
        pair: Pair<'a, Rule>,
        builder: InitializedGeneralThresholdAutomatonBuilder,
        ctx: &mut TLAParsingContext,
    ) -> Result<InitializedGeneralThresholdAutomatonBuilder, anyhow::Error> {
        debug_assert!(
            pair.as_rule() == Rule::assume_declaration,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str()
        );
        let err_context_msg = "Failed to parse 'ASSUME' / resilience condition: ";

        let mut inner_pairs = pair.into_inner();
        let inner_pair = inner_pairs.next().expect("Missing: condition for assume");
        let inner_span = inner_pair.as_span();

        debug_assert!(inner_pairs.next().is_none());

        let rc_cond =
            parse_int_boolean_expr(inner_pair, &builder, ctx).with_context(|| err_context_msg);

        let mut rc_split = split_conjunct_bool_expr(rc_cond.unwrap());
        validate_and_add_n_corr_proc_constr(ctx, &mut rc_split, inner_span)
            .with_context(|| err_context_msg)?;

        let builder = builder
            .with_resilience_conditions(rc_split)
            .with_context(|| err_context_msg)?;

        Ok(builder)
    }

    /// Parse a variable declaration, i.e. the `VARIABLE` / `VARIABLES`
    /// declaration of of a TLA file
    ///
    /// This declaration needs to declare all shared variables of the resulting
    /// TA, as well as the variable 'ProcessesLocations' which is the function
    /// from process identifiers to their current location.
    fn parse_variable_declaration<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: GeneralThresholdAutomatonBuilder,
    ) -> Result<(Pair<'a, Rule>, GeneralThresholdAutomatonBuilder), anyhow::Error> {
        if pair.as_rule() != Rule::variable_declaration {
            warn!(
                "Did not find any declared shared variables. Variables must be \
declared using 'VARIABLE' / 'VARIABLES' declaration."
            );
            return Ok((pair, builder));
        }

        let mut inner_pairs = pair.into_inner();
        let inner_pair = inner_pairs.next().unwrap();

        let mut shared_vars: Vec<Variable> = parse_identifier_list_to_t(inner_pair);

        if !shared_vars.contains(&Variable::new(LOCATIONS_SET)) {
            return Err(anyhow!(
                "Missing special variable '{LOCATIONS_SET}': No declaration for \
variable '{LOCATIONS_SET}' which is used to declares the set of locations. \
Please add a declaration for variable '{LOCATIONS_SET}'."
            ));
        }

        debug!(
            "TLA file declares constants: {}",
            join_iterator(shared_vars.iter(), ", ")
        );

        shared_vars.retain(|v| v != &Variable::new(LOCATIONS_SET));

        let builder = builder.with_variables(shared_vars)?;

        let pair = pairs.next().expect("Missing: TypeOk");

        Ok((pair, builder))
    }

    /// Parse the `TypeOk` block into the set of locations and validates that it
    /// declares a type for all shared variables, that should be declared as
    /// type 'Nat'.
    fn parse_type_ok<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: GeneralThresholdAutomatonBuilder,
    ) -> Result<(Pair<'a, Rule>, InitializedGeneralThresholdAutomatonBuilder), anyhow::Error> {
        debug_assert!(
            pair.as_rule() == Rule::typeok_declaration,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str()
        );
        let ctx_err_msg = "Error while parsing correctness \
constraint 'TypeOk': ";

        let mut variables_declared_nat = Vec::new();
        let mut set_of_locs = Vec::new();

        for set_expr in pair.into_inner() {
            debug_assert!(set_expr.as_rule() == Rule::set_boolean_expr);

            let mut inner_pairs = set_expr.into_inner();

            let ident: Variable = parse_identifier_to_t(
                &inner_pairs
                    .next()
                    .expect("Invalid set_boolean_expr: Missing identifier"),
            );
            let set_expr = inner_pairs
                .next()
                .expect("Invalid set_boolean_expr: Missing set");

            // Parse special declaration of the type of ProcessesLocation to the
            // set of locations of the threshold automaton
            if ident == Variable::new(LOCATIONS_SET) {
                if !set_of_locs.is_empty() {
                    return new_parsing_error_with_ctx(
                        "Second declaration of set of locations found: ",
                        set_expr.as_span(),
                        ctx_err_msg,
                    );
                }

                set_of_locs = parse_set_of_locations(set_expr).with_context(|| ctx_err_msg)?;
                continue;
            }

            if set_expr.as_rule() != Rule::nat {
                return new_parsing_error_with_ctx(
                    format!(
                        "Shared variables are expected to be of type 'Nat' but \
'{}'  is declared as type '{}'.",
                        ident.name(),
                        set_expr.as_str()
                    ),
                    set_expr.as_span(),
                    ctx_err_msg,
                );
            }

            variables_declared_nat.push((ident, set_expr));
        }

        let builder = builder.with_locations(set_of_locs)?;

        let pair = pairs.next().expect("Missing: init constraint");
        let builder = builder.initialize();

        // Check that all variables which have a type declaration have been declared first
        for (var, expr) in variables_declared_nat {
            if !builder.has_variable(&var) {
                return new_parsing_error_with_ctx(
                    format!(
                        "Type declaration for unknown variable '{}' found",
                        var.name()
                    ),
                    expr.as_span(),
                    ctx_err_msg,
                );
            }
        }

        Ok((pair, builder))
    }

    /// Parse the initial constraints of an `Init` block
    fn parse_initial_constraint_declaration<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: InitializedGeneralThresholdAutomatonBuilder,
        ctx: &mut TLAParsingContext,
    ) -> Result<
        (
            Option<Pair<'a, Rule>>,
            InitializedGeneralThresholdAutomatonBuilder,
        ),
        anyhow::Error,
    > {
        if pair.as_rule() != Rule::init_constraint_declaration {
            debug!("No initial constraints have been found in TLA file");
            return Ok((Some(pair), builder));
        }
        let err_context_msg = "Error while parsing  initial constraints /
'Init': ";

        let inner_pairs = pair.into_inner();

        let mut builder = builder;

        for init_constr in inner_pairs {
            debug_assert!(init_constr.as_rule() == Rule::init_constraint_expr);

            let mut inner_pairs = init_constr.into_inner();
            let inner_pair = inner_pairs.next().expect("Expected initial constraint");

            if inner_pair.as_rule() == Rule::int_bool_expr {
                let var_expr = parse_int_boolean_expr(inner_pair, &builder, ctx)
                    .with_context(|| err_context_msg)?;
                // Split first-level conjuncts for nicer representation
                let split_var_expr = split_conjunct_bool_expr(var_expr);

                builder = builder
                    .with_initial_variable_constraints(split_var_expr)
                    .with_context(|| err_context_msg)?;
                continue;
            }

            if inner_pair.as_rule() == Rule::set_boolean_expr {
                let loc_constr = parse_initial_loc_constr(inner_pair, &builder, ctx)?;
                builder = builder
                    .with_initial_location_constraints(loc_constr)
                    .with_context(|| err_context_msg)?;
                continue;
            }

            debug_assert!(false, "Expected location or variable expression")
        }

        let pair = pairs.next();
        Ok((pair, builder))
    }

    /// Parse all consecutive declaration of integer macros
    fn parse_int_macro_declarations<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Option<Pair<'a, Rule>>,
        ctx: &mut TLAParsingContext<'a>,
    ) -> Option<Pair<'a, Rule>> {
        let mut opt_pair = pair;
        while opt_pair.is_some() {
            let pair = opt_pair.unwrap();
            if pair.as_rule() != Rule::int_macro_declaration {
                opt_pair = Some(pair);
                break;
            }

            let mut inner_pairs = pair.into_inner();

            let ident_pair = inner_pairs.next().expect("Missing: macro ident");
            let ident: String = parse_identifier_to_t(&ident_pair);

            let expr_pair = inner_pairs.next().expect("Missing: integer macro int expr");
            debug_assert!(expr_pair.as_rule() == Rule::integer_expr);

            debug!(
                "TLA file declared integer macro: '{ident}' := '{}'",
                expr_pair.as_str()
            );

            ctx.int_macro.insert(ident, expr_pair);
            opt_pair = pairs.next()
        }

        opt_pair
    }

    /// Parse all consecutive declarations of rules
    fn parse_rule_declarations<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: InitializedGeneralThresholdAutomatonBuilder,
        ctx: &mut TLAParsingContext<'a>,
    ) -> Result<
        (
            Option<Pair<'a, Rule>>,
            InitializedGeneralThresholdAutomatonBuilder,
        ),
        anyhow::Error,
    > {
        let mut opt_pair = Some(pair);
        let mut builder = builder;

        while opt_pair.is_some() {
            let pair = opt_pair.unwrap();
            if pair.as_rule() != Rule::rule_declaration {
                opt_pair = Some(pair);
                break;
            }

            let rule_span = pair.as_span();
            let mut inner_pairs = pair.into_inner();

            let id_pair = inner_pairs.next().expect("Missing: rule_ident");
            let (id, proc_ident) = parse_rule_ident_to_id_and_proc_ident(id_pair);

            let rule =
                parse_rule_body_exprs(inner_pairs, rule_span, &builder, id, &proc_ident, ctx)?;
            debug!("TLA file declared rule: {rule}");
            builder = builder
                .with_rule(rule)
                .with_context(|| "Error while parsing rule: ")?;

            opt_pair = pairs.next();
        }

        Ok((opt_pair, builder))
    }

    /// Parse a `Next` declaration and extract all appearing rules
    fn parse_next_declaration<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Option<Pair<'a, Rule>>,
        ctx: &mut TLAParsingContext,
    ) -> Result<Option<Pair<'a, Rule>>, anyhow::Error> {
        if pair.is_none() {
            return Ok(pair);
        }

        let pair = pair.unwrap();
        if pair.as_rule() != Rule::next_declaration {
            return Ok(Some(pair));
        }

        if !ctx.rule_ids_in_next.is_empty() {
            return new_parsing_error_with_ctx(
                "Duplicate next declaration found.",
                pair.as_span(),
                "Error while parsing 'Next' specification",
            );
        }

        let rules = parse_next_expr(pair)?;
        ctx.rule_ids_in_next.extend(rules);

        Ok(pairs.next())
    }

    /// Parse a `Spec` declaration and validate that it is consistent
    fn validate_spec_declaration<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Option<Pair<'a, Rule>>,
        ctx: &mut TLAParsingContext,
        builder: &InitializedGeneralThresholdAutomatonBuilder,
    ) -> Result<Option<Pair<'a, Rule>>, anyhow::Error> {
        if pair.is_none() {
            return Ok(None);
        }

        let pair = pair.unwrap();
        let pair_span = pair.as_span();
        if pair.as_rule() != Rule::spec_declaration {
            return Ok(Some(pair));
        }
        let err_ctx_msg = "Error while parsing Spec declaration: ";

        if ctx.spec_declaration_parsed {
            return new_parsing_error_with_ctx(
                "Duplicate definition of 'Spec'.",
                pair_span,
                err_ctx_msg,
            );
        }
        ctx.spec_declaration_parsed = true;

        let mut inner_pairs = pair.into_inner();
        let vars_referenced: Vec<Variable> =
            parse_identifier_list_to_t(inner_pairs.next().expect("Missing: Updated params"));

        let proc_var = Variable::new(LOCATIONS_SET);

        if let Some(var) = vars_referenced
            .iter()
            .find(|v| *v != &proc_var && !builder.is_declared(*v))
        {
            return new_parsing_error_with_ctx(
                format!("Undeclared variable '{var}'"),
                pair_span,
                err_ctx_msg,
            );
        }

        if let Some(var) = builder.variables().find(|v| !vars_referenced.contains(v)) {
            return new_parsing_error_with_ctx(
                format!("Next instantiation does not include variable '{var}'"),
                pair_span,
                err_ctx_msg,
            );
        }

        if !vars_referenced.contains(&proc_var) {
            return new_parsing_error_with_ctx(
                format!(
                    "Next instantiation does not include the location of processes represented by variable '{LOCATIONS_SET}'"
                ),
                pair_span,
                err_ctx_msg,
            );
        }

        Ok(pairs.next())
    }
}

/// Validate and remove constraints on special parameter N_CORR_PROC
///
/// The function will parse the constraint into an integer expression and add it
/// to the parsing context.
fn validate_and_add_n_corr_proc_constr(
    ctx: &mut TLAParsingContext,
    rcs: &mut Vec<BooleanExpression<Parameter>>,
    span: Span<'_>,
) -> Result<(), anyhow::Error> {
    let err_ctx_msg = "Error while validating assumptions on the number  correct processes";

    for rc in rcs {
        match rc {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                let mut other_expr = None;
                if lhs.as_ref() == &IntegerExpression::Atom(Parameter::new(N_CORR_PROC))
                    || lhs.as_ref() == &IntegerExpression::Param(Parameter::new(N_CORR_PROC))
                {
                    other_expr = Some(*rhs.clone());
                }

                if rhs.as_ref() == &IntegerExpression::Atom(Parameter::new(N_CORR_PROC))
                    || rhs.as_ref() == &IntegerExpression::Param(Parameter::new(N_CORR_PROC))
                {
                    other_expr = Some(*lhs.clone())
                }
                if other_expr.is_none() {
                    continue;
                }

                let other_expr = other_expr.unwrap();

                if other_expr.contains_atom_a(&Parameter::new(N_CORR_PROC))
                    || op != &ComparisonOp::Eq
                {
                    return new_parsing_error_with_ctx(
                        format!(
                            "Invalid declaration of the number of correct \
processes '{}{}{}' does not specify a concrete number of correct processes. \
Expected constraint of the form '{N_CORR_PROC} == <EXPR>' where <EXPR> is an \
integer expression over the parameters of the threshold automaton",
                            lhs, op, rhs
                        ),
                        span,
                        err_ctx_msg,
                    );
                }

                if ctx.param_to_corr_procs.is_some() {
                    return new_parsing_error_with_ctx(
                        format!(
                            "Found second constraint on the number of correct \
processes: '{}{}{}'. There can only be one constraint on '{N_CORR_PROC}'!",
                            lhs, op, rhs
                        ),
                        span,
                        err_ctx_msg,
                    );
                }

                debug!(
                    "TLA file declares the number of correct processes as: {}",
                    other_expr
                );

                ctx.param_to_corr_procs = Some(other_expr.into());
                *rc = BooleanExpression::True;
            }
            BooleanExpression::BinaryExpression(_, BooleanConnective::And, _) => {
                debug_assert!(
                    false,
                    "Boolean expression should have been split before validation!"
                );
            }
            _ => {}
        }
    }

    Ok(())
}

/// Parse a constraint over ` ProcessesLocations` into the set of initial
/// locations
///
/// This function is meant to parse a constraint of the form
/// `ProcessesLocations \in [Processes -> {"loc0", "loc1"}]`
/// appearing in the initial constraints and derive the boolean expressions that
/// are necessary to represent the initial constraints.
fn parse_initial_loc_constr(
    pair: Pair<'_, Rule>,
    builder: &InitializedGeneralThresholdAutomatonBuilder,
    ctx: &mut TLAParsingContext,
) -> Result<Vec<BooleanExpression<Location>>, anyhow::Error> {
    let err_ctx_msg = "Error while parsing set of locations: ";
    let mut inner_pairs = pair.into_inner();

    let ident_pair = &inner_pairs
        .next()
        .expect("Invalid set_bool_expr: Missing identifier");
    let ident: Variable = parse_identifier_to_t(ident_pair);
    if ident != Variable::new(LOCATIONS_SET) {
        return new_parsing_error_with_ctx(
            "Set constraint found that is not over the locations of processes",
            ident_pair.as_span(),
            err_ctx_msg,
        );
    }

    let set_expr = inner_pairs
        .next()
        .expect("Invalid set_bool_expr: Missing set");

    let init_locs = parse_set_of_locations(set_expr).with_context(|| err_ctx_msg)?;

    debug!(
        "TLA file declares the following locations as initial: {}",
        join_iterator(init_locs.iter(), ", ")
    );

    // Add constraint for all locations that are not initial, setting them to 0
    let not_init_locs = builder
        .locations()
        .filter(|l| !init_locs.contains(l))
        .map(|l| {
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(l.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )
        });

    if init_locs.is_empty() {
        warn!("No initial location found!");
        return Ok(not_init_locs.collect());
    }

    // Sum over all initial locations
    let first_loc = IntegerExpression::Atom(init_locs[0].clone());
    let init_loc_sum = init_locs.iter().skip(1).fold(first_loc, |acc, l| {
        IntegerExpression::BinaryExpr(
            Box::new(acc),
            IntegerOp::Add,
            Box::new(IntegerExpression::Atom(l.clone())),
        )
    });

    // constraint specifying that the correct number of processes starts in the initial location
    let init_proc_constr = BooleanExpression::ComparisonExpression(
        Box::new(init_loc_sum),
        ComparisonOp::Eq,
        Box::new(ctx.param_to_corr_procs.clone().unwrap()),
    );

    let mut loc_constr = vec![init_proc_constr];
    loc_constr.extend(not_init_locs);

    Ok(loc_constr)
}

/// Parse the location declaration in 'TypeOk' or in 'Init' into a set of
/// locations
fn parse_set_of_locations<'a>(pair: Pair<'a, Rule>) -> Result<Vec<Location>, anyhow::Error> {
    let ctx_err_msg = "Error while parsing the list of locations: ";

    if pair.as_rule() != Rule::map_definition {
        return new_parsing_error_with_ctx(
            format!(
                "The type of '{LOCATIONS_SET}' is expected to be a map from the \
set of processes '{PROC_SET}' to the set of locations, specified as a set of \
strings"
            ),
            pair.as_span(),
            ctx_err_msg,
        );
    }

    let mut pairs: Pairs<'_, Rule> = pair.into_inner();

    let ident_pair = pairs.next().expect("Missing: identifier");
    let ident: String = parse_identifier_to_t(&ident_pair);
    if ident != PROC_SET {
        return new_parsing_error_with_ctx(
            format!(
                "The type of '{LOCATIONS_SET}' is expected to be a map from the \
set of processes '{PROC_SET}' to the set of locations. Instead it is a map \
from unknown set {ident}"
            ),
            ident_pair.as_span(),
            ctx_err_msg,
        );
    }

    let set_pair = pairs.next().expect("Missing: set definition");
    if set_pair.as_rule() != Rule::set_definition_identifier_list {
        return new_parsing_error_with_ctx(
            format!(
                "The type of '{LOCATIONS_SET}' is expected to be a map from \
the set of processes '{PROC_SET}' to the set of locations, specified as pair \
of strings. Location set has an unexpected form."
            ),
            set_pair.as_span(),
            ctx_err_msg,
        );
    }

    let mut inner_pairs = set_pair.into_inner();
    let inner_pair = inner_pairs.next().expect("Location set cannot be empty");

    let locations = parse_identifier_list_to_t(inner_pair);

    debug!(
        "TLA file declared the following locations: {}",
        join_iterator(locations.iter(), ", ")
    );

    Ok(locations)
}

/// Parse all rule body expressions
///
/// Parses all pairs of type `rule_body_expr` into a consistent rule
fn parse_rule_body_exprs<'a>(
    pairs: Pairs<'a, Rule>,
    rule_span: Span<'a>,
    builder: &InitializedGeneralThresholdAutomatonBuilder,
    rule_id: u32,
    proc_ident: &String,
    ctx: &mut TLAParsingContext<'a>,
) -> Result<general_threshold_automaton::Rule, anyhow::Error> {
    let ctx_err_msg = format!("Error while parsing rule {rule_id}");

    let pair_vec = pairs.collect::<Vec<_>>();

    // Parse the source of the rule
    let src_pair = pair_vec
        .iter()
        .filter(|p| p.as_rule() == Rule::map_boolean_expr)
        .collect::<Vec<_>>();
    if src_pair.is_empty() {
        return new_parsing_error_with_ctx(
            "Missing: Definition of source location",
            rule_span,
            ctx_err_msg,
        );
    }
    if src_pair.len() > 1 {
        return new_parsing_error_with_ctx(
            format!(
                "Two declarations of target locations found in rule {rule_id}. Target constraints: {}",
                join_iterator(src_pair.iter().map(|p| p.as_str()), ",")
            ),
            rule_span,
            ctx_err_msg,
        );
    }
    let source = try_parse_map_entry_constr_loc(src_pair[0].clone(), proc_ident)
        .with_context(|| ctx_err_msg.clone())?;

    // Parse the target of the rule
    let target_pair = pair_vec
        .iter()
        .filter(|p| p.as_rule() == Rule::map_update_expr)
        .collect::<Vec<_>>();
    if target_pair.is_empty() {
        return new_parsing_error_with_ctx(
            "Missing: Definition of target location",
            rule_span,
            ctx_err_msg,
        );
    }
    if target_pair.len() > 1 {
        return new_parsing_error_with_ctx(
            format!(
                "Two declarations of target locations found in rule {rule_id}. Target constraints: {}",
                join_iterator(target_pair.iter().map(|p| p.as_str()), ", ")
            ),
            rule_span,
            ctx_err_msg,
        );
    }
    let target = parse_map_update_to_target_location(target_pair[0].clone(), proc_ident)
        .with_context(|| ctx_err_msg.clone())?;

    let mut rule_builder = RuleBuilder::new(rule_id, source, target);

    // Parse the guard conditions of the rule
    let guard_conditions = pair_vec
        .iter()
        .filter(|p| p.as_rule() == Rule::int_bool_expr)
        .map(|p| parse_int_boolean_expr(p.clone(), builder, ctx))
        .collect::<Result<Vec<BooleanExpression<Variable>>, _>>()
        .with_context(|| ctx_err_msg.clone())?;

    // Build the conjunction of the guards
    let mut first = BooleanExpression::True;
    if !guard_conditions.is_empty() {
        first = guard_conditions[0].clone();
    }
    let guard = guard_conditions.into_iter().skip(1).fold(first, |acc, x| {
        BooleanExpression::BinaryExpression(Box::new(acc), BooleanConnective::And, Box::new(x))
    });
    rule_builder = rule_builder.with_guard(guard);

    // Parse actions
    let rule_updates = pair_vec
        .iter()
        .filter(|p| p.as_rule() == Rule::integer_update)
        .map(|p| parse_integer_update_expr(p.clone(), builder, ctx))
        .collect::<Result<Vec<_>, _>>()
        .with_context(|| ctx_err_msg.clone())?
        .into_iter()
        .flatten();

    // add actions to the rule
    rule_builder = rule_builder.with_actions(rule_updates);

    Ok(rule_builder.build())
}

/// Parse a map update / map redefinition to the target location of a rule
///
/// Example of a map redefinition:
/// `ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locEC"]`
fn parse_map_update_to_target_location(
    pair: Pair<'_, Rule>,
    proc_ident: &String,
) -> Result<Location, anyhow::Error> {
    debug_assert!(
        pair.as_rule() == Rule::map_update_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pair_span = pair.as_span();
    let mut inner_pairs = pair.into_inner();

    let map_ident: String = parse_identifier_to_t(&inner_pairs.next().unwrap());
    if map_ident != LOCATIONS_SET {
        return new_parsing_error_with_ctx(
            format!(
                "Unknown map update. Only location map '{LOCATIONS_SET}' can be \
updated (Example: \
'{LOCATIONS_SET}' = [{LOCATIONS_SET} EXCEPT ![{proc_ident}] = \"loc0\"')."
            ),
            pair_span,
            "Error while parsing rule body: ",
        );
    }

    let map_pair = inner_pairs.next().expect("Missing: map redefinition");

    try_parse_map_redef_to_target_loc(map_pair, proc_ident)
}

/// Helper function to [parse_map_update_to_target_location]
fn try_parse_map_redef_to_target_loc(
    pair: Pair<'_, Rule>,
    proc_ident: &String,
) -> Result<Location, anyhow::Error> {
    debug_assert!(
        pair.as_rule() == Rule::map_redefinition,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    let ctx_err_msg = "Error while parsing rule body: ";

    let pair_span = pair.as_span();
    let mut inner_pairs = pair.into_inner();

    let map_ident: String = parse_identifier_to_t(&inner_pairs.next().unwrap());
    if map_ident != LOCATIONS_SET {
        return new_parsing_error_with_ctx(
            format!(
                "Unknown map update. Only location map '{LOCATIONS_SET}' can be \
updated (Example: \
'{LOCATIONS_SET}' = [{LOCATIONS_SET} EXCEPT ![{proc_ident}] = \"loc0\"')."
            ),
            pair_span,
            ctx_err_msg,
        );
    }

    let parsed_elem_name: String = parse_identifier_to_t(&inner_pairs.next().unwrap());
    if &parsed_elem_name != proc_ident {
        return new_parsing_error_with_ctx(
            format!(
                "Unknown element used in index of the map: got \
'{parsed_elem_name}', expected '{proc_ident}'"
            ),
            pair_span,
            ctx_err_msg,
        );
    }

    let loc: Location = parse_identifier_to_t(&inner_pairs.next().unwrap());
    Ok(loc)
}

/// Parses a `map_boolean_expr` into a [Location]
///
/// Example: `ProcessesLocations\[p\] = "loc1"`
fn try_parse_map_entry_constr_loc<T: Atomic + 'static>(
    pair: Pair<'_, Rule>,
    proc_ident: &String,
) -> Result<T, anyhow::Error> {
    debug_assert!(
        pair.as_rule() == Rule::map_boolean_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    let ctx_err_msg = "Error while parsing rule body: ";

    let mut inner_pairs = pair.into_inner();

    let map_entry_pair = inner_pairs.next().expect("Missing: map entry");
    let map_entry_span = map_entry_pair.as_span();
    let (map_name, parsed_proc_name) =
        parse_map_entry_into_map_ident_and_proc_ident(map_entry_pair);

    if map_name != LOCATIONS_SET {
        return new_parsing_error_with_ctx(
            format!(
                "Unknown map condition. Source location should be specified by \
constraining valuation of in '{LOCATIONS_SET}' (Example: \
'{LOCATIONS_SET}[{proc_ident}] = \"{proc_ident}\"')"
            ),
            map_entry_span,
            ctx_err_msg,
        );
    }

    if proc_ident != &parsed_proc_name {
        return new_parsing_error_with_ctx(
            format!(
                "Unknown element used in index of the map: got \
'{parsed_proc_name}', expected '{proc_ident}'"
            ),
            map_entry_span,
            ctx_err_msg,
        );
    }

    let loc = parse_identifier_to_t(&inner_pairs.next().expect("Missing: loc"));

    Ok(loc)
}

/// Parse all rule ids appearing in a `Next` expression
fn parse_next_expr(pair: Pair<'_, Rule>) -> Result<Vec<u32>, anyhow::Error> {
    debug_assert!(
        pair.as_rule() == Rule::next_declaration,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let mut inner_pairs = pair.into_inner();

    let elem_ident_pair = inner_pairs.next().expect("Missing: process identifier");
    let proc_ident: String = parse_identifier_to_t(&elem_ident_pair);

    let mut found_ids = Vec::new();
    // Parse rule ids specified in next
    for pair in inner_pairs {
        let pair_span = pair.as_span();
        let (id, parsed_proc_ident) = parse_rule_ident_to_id_and_proc_ident(pair);

        if parsed_proc_ident != proc_ident {
            return new_parsing_error_with_ctx(
                format!(
                    "Unknown process identifier '{parsed_proc_ident}' (expected previously declared process dentifier '{proc_ident}'"
                ),
                pair_span,
                "Error while parsing next constraint: ",
            );
        }

        found_ids.push(id);
    }

    Ok(found_ids)
}

/// Parses a `map_entry`  into the name of the map and the identifier of the
/// element used as an index in the map
fn parse_map_entry_into_map_ident_and_proc_ident(pair: Pair<'_, Rule>) -> (String, String) {
    debug_assert!(
        pair.as_rule() == Rule::map_entry,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    let mut inner_pairs = pair.into_inner();

    let map_ident: String = parse_identifier_to_t(&inner_pairs.next().unwrap());
    let proc_ident: String = parse_identifier_to_t(&inner_pairs.next().unwrap());

    (map_ident, proc_ident)
}

/// Parse the rule id out of the rule name and collect the name of the identifier
/// used for specifying the process identifier
///
/// # Example
///
/// For example `Rule0(p)` will be parsed to the tuple (0, "p").
fn parse_rule_ident_to_id_and_proc_ident(pair: Pair<'_, Rule>) -> (u32, String) {
    debug_assert!(
        pair.as_rule() == Rule::rule_identifier,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    let mut inner_pairs = pair.into_inner();

    let id_pair = inner_pairs.next().expect("Missing: rule id");
    let id = parse_integer_const(id_pair);

    let proc_ident_pair = inner_pairs
        .next()
        .expect("Missing: rule process identifier");
    let proc_ident: String = parse_identifier_to_t(&proc_ident_pair);

    (id, proc_ident)
}

/// Split a conjunction of boolean expressions into a vector
///
/// This function splits only conjuncts on the top level !
/// It does not transform expressions into CNF
fn split_conjunct_bool_expr<T: Atomic>(bexpr: BooleanExpression<T>) -> Vec<BooleanExpression<T>> {
    match bexpr {
        BooleanExpression::BinaryExpression(lhs, BooleanConnective::And, rhs) => {
            let mut lhs = split_conjunct_bool_expr(*lhs);
            let rhs = split_conjunct_bool_expr(*rhs);
            lhs.extend(rhs);
            lhs
        }
        s => vec![s],
    }
}

/// Parse a list of identifiers into a vector of objects of type T
#[inline(always)]
fn parse_identifier_list_to_t<T: for<'a> From<&'a str>>(pair: Pair<'_, Rule>) -> Vec<T> {
    debug_assert!(
        pair.as_rule() == Rule::identifier_list || pair.as_rule() == Rule::string_identifier_list,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    pair.into_inner()
        .map(|id| parse_identifier_to_t(&id))
        .collect()
}

/// Parse an identifier into an object of type T
#[inline(always)]
fn parse_identifier_to_t<T: for<'a> From<&'a str>>(pair: &Pair<'_, Rule>) -> T {
    debug_assert!(
        pair.as_rule() == Rule::identifier,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    T::from(pair.as_str())
}

/// Generate a new parsing error and add context
#[inline(always)]
fn new_parsing_error_with_ctx<T, S: Into<String>, SI: Into<String>>(
    err_msg: S,
    span: Span<'_>,
    ctx_msg: SI,
) -> Result<T, anyhow::Error> {
    let err_msg = err_msg.into();
    let parse_err: Box<pest::error::Error<Rule>> = Box::new(pest::error::Error::new_from_span(
        pest::error::ErrorVariant::CustomError { message: err_msg },
        span,
    ));

    let ctx_msg = ctx_msg.into();
    Err(parse_err).with_context(|| ctx_msg)
}

/// Generate a new parsing error
#[inline(always)]
fn new_parsing_error<S: Into<String>>(message: S, span: Span<'_>) -> Box<pest::error::Error<()>> {
    let message = message.into();
    Box::new(pest::error::Error::new_from_span(
        pest::error::ErrorVariant::CustomError { message },
        span,
    ))
}

#[cfg(test)]
mod tests {

    use pest::Parser;

    use crate::{
        ParseTA, ParseTAWithLTL,
        bymc::ByMCParser,
        tla::{PestTLAParser, Rule, TLAParser},
    };

    #[test]
    fn test_var_dec_parses() {
        let input =
            "VARIABLES ProcessesLocations, nsnt00, nsnt01, nsnt10,  nsnt11,  nsnt00plus01, nfaulty";

        let _pairs = PestTLAParser::parse(Rule::variable_declaration, input);
    }

    #[test]
    fn test_parse_min_working() {
        let input = "
-------------------------------- MODULE aba --------------------------------
CONSTANT Processes, NbOfCorrProc, n

ASSUME NbOfCorrProc = 0

VARIABLES ProcessesLocations

TypeOk ==
/\\ ProcessesLocations \\in [Processes -> {\"loc\"}]
";

        let parser = TLAParser::default();
        let res = parser.parse_ta_and_spec(input);
        let (got_ta, got_ltl) = res.unwrap();
        let got_ta_2 = TLAParser::default().parse_ta(input).unwrap();

        let expected_ta = "\
ta tla_ta {
    parameters n;

    assumptions (1) {
        true;
    }

    locations (5) {
        loc: [0];
    }

    inits (0) {
    }

    rules (0) {
    }

    spec(0) {
    }
        
}";
        let (expected_ta, expected_ltl) = ByMCParser::new().parse_ta_and_spec(expected_ta).unwrap();

        assert_eq!(
            got_ta, expected_ta,
            "expected:\n{expected_ta}\n\ngot:\n{got_ta}"
        );
        assert_eq!(
            got_ta_2, expected_ta,
            "expected:\n{expected_ta}\n\ngot:\n{got_ta}"
        );
        assert_eq!(
            got_ltl, expected_ltl,
            "expected:\n{expected_ltl}\n\ngot:\n{got_ltl}"
        )
    }

    #[test]
    fn test_parse_full_spec() {
        let input = "
-------------------------------- MODULE aba --------------------------------

EXTENDS Integers, FiniteSets

CONSTANT
Processes,
NbOfCorrProc,
N,
T,
F

ASSUME
/\\ NbOfCorrProc = N - F
/\\ N > 3 * T
/\\ T >= F
/\\ T >= 1

VARIABLES
ProcessesLocations,
nsntEC,
nsntRD


TypeOk ==
/\\ ProcessesLocations \\in [Processes -> {\"loc0\", \"loc1\", \"locEC\", \"locRD\", \"locAC\"}]
/\\ nsntEC \\in Nat
/\\ nsntRD \\in Nat 



Init ==
/\\ ProcessesLocations \\in [Processes -> {\"loc0\", \"loc1\"}] 
/\\ nsntEC = 0
/\\ nsntRD = 0

------------------------------------------------------------------------------------------

Rule0(p) ==
                    /\\ ProcessesLocations[p] = \"loc1\"
                    /\\ ProcessesLocations\' = [ProcessesLocations EXCEPT ![p] = \"locEC\"]
                    /\\ nsntEC' = nsntEC + 1                   
                    /\\ UNCHANGED <<nsntRD>>
----------------------------------------------------------------------------------------
Rule1(p) ==
                     /\\ ProcessesLocations[p] = \"loc0\"
                     /\\ 2 * nsntEC >= N + T + 1 - 2 * F
                     /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locEC\"]
                     /\\ nsntEC' = nsntEC + 1                    
                     /\\ UNCHANGED <<nsntRD>>

----------------------------------------------------------------------------------------
Rule2(p) ==
                    /\\ ProcessesLocations[p] = \"loc0\"
                    /\\ nsntRD >= T + 1 - F
                    /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locEC\"]
                    /\\ nsntEC' = nsntEC + 1
                    /\\ UNCHANGED <<nsntRD>>
                    
----------------------------------------------------------------------------------------
Rule3(p) ==
                     /\\ ProcessesLocations[p] = \"locEC\"
                     /\\ 2 * nsntEC >= N + T + 1 - 2 * F
                     /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locRD\"]
                     /\\ nsntRD' = nsntRD + 1
                     /\\ UNCHANGED << nsntEC>>
                     
----------------------------------------------------------------------------------------
Rule4(p) ==
                     /\\ ProcessesLocations[p] = \"locEC\"
                     /\\ nsntRD >= T + 1 - F
                     /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locRD\"]
                     /\\ nsntRD' = nsntRD + 1
                     /\\ UNCHANGED << nsntEC>>
------------------------------------------------------------------------

Rule5(p) ==
                     /\\ ProcessesLocations[p] = \"locRD\"
                     /\\ 2 * nsntRD >= 2 * T + 1
                     /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locAC\"]
                     /\\ UNCHANGED <<nsntEC, nsntRD>>
----------------------------------------------------------------------------------------
Rule6(p) ==
                    /\\ ProcessesLocations[p] = \"loc0\"
                    /\\ 2 * nsntEC < N + T + 1
                    /\\ nsntRD < T + 1
                    /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"loc0\"]
                    /\\ UNCHANGED <<nsntEC, nsntRD>>
----------------------------------------------------------------------------------------                    
                    
 Rule7(p) ==
                    /\\ ProcessesLocations[p] = \"locEC\"
                    /\\ 2 * nsntEC < N + T + 1
                    /\\ nsntRD < T + 1
                    /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locEC\"]
                    /\\ UNCHANGED << nsntEC, nsntRD>>

----------------------------------------------------------------------------------------
Rule8(p) ==
                     /\\ ProcessesLocations[p] = \"locRD\"
                     /\\ nsntRD < 2 * T + 1
                     /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locRD\"]
                     /\\ UNCHANGED <<nsntEC, nsntRD>>


----------------------------------------------------------------------------------------
Rule9(p) ==
                    /\\ ProcessesLocations[p] = \"locAC\"
                    /\\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = \"locAC\"]
                    /\\ UNCHANGED <<nsntEC, nsntRD>> 

----------------------------------------------------------------------------------------

NumInloc0 == Cardinality({p \\in Processes : ProcessesLocations[p] = \"loc0\"})
NumInloc1 == Cardinality({p \\in Processes : ProcessesLocations[p] = \"loc1\"})
NumInlocEC == Cardinality({p \\in Processes : ProcessesLocations[p] = \"locEC\"})
NumInlocAC == Cardinality({p \\in Processes : ProcessesLocations[p] = \"locAC\"})                    
NumInlocRD == Cardinality({p \\in Processes : ProcessesLocations[p] = \"locRD\"}) 
                                      
unforg == 
        NumInloc1 = 0 => [] (NumInlocAC = 0)
        
corr ==
  <>[](
    (((2 * nsntEC < N + T + 1) \\/ (NumInloc0 = 0))
     /\\ ((nsntRD < T + 1) \\/ (NumInloc0 = 0))
     /\\ ((2 * nsntEC < N + T + 1) \\/ (NumInlocEC = 0))
     /\\ ((nsntRD < T + 1) \\/ (NumInlocEC = 0))
     /\\ ((nsntRD < 2 * T + 1) \\/ (NumInlocRD = 0))
     /\\ (NumInloc1 = 0))
    => ((NumInloc0 = 0) => <> (NumInlocAC /= 0))
  )
  
 agreement ==
  <>[](
    (((2 * nsntEC < N + T + 1) \\/ (NumInloc0 = 0))
     /\\ ((nsntRD < T + 1) \\/ (NumInloc0 = 0))
     /\\ ((2 * nsntEC < N + T + 1) \\/ (NumInlocEC = 0))
     /\\ ((nsntRD < T + 1) \\/ (NumInlocEC = 0))
     /\\ ((nsntRD < 2 * T + 1) \\/ (NumInlocRD = 0))
     /\\ (NumInloc1 = 0))
    =>
    [](
      (NumInlocAC /= 0)
      => <>((NumInloc0 = 0) /\\ (NumInloc1 = 0) /\\ (NumInlocEC = 0) /\\ (NumInlocRD = 0))
    )
  )
  
        
----------------------------------------------------------------------------------------
Next == \\E p \\in Processes:
                            \\/ Rule0(p)
                            \\/ Rule1(p)
                            \\/ Rule2(p)
                            \\/ Rule3(p)
                            \\/ Rule4(p)
                            \\/ Rule5(p)
                            \\/ Rule6(p)
                            \\/ Rule7(p)
                            \\/ Rule8(p)
                            \\/ Rule9(p)


Spec == Init /\\ [][Next]_<< ProcessesLocations, nsntEC, nsntRD >>
=============================================================================
";

        let parser = TLAParser::default();
        let res = parser.parse_ta_and_spec(input);
        let (got_ta, got_ltl) = res.unwrap();
        let got_ta_2 = TLAParser::default().parse_ta(input).unwrap();

        let expected_ta = "\
ta tla_ta {
    shared nsntEC, nsntRD;

    parameters N, T, F;

    assumptions (4) {
        true;
        N > (3 * T);
        T >= F;
        T >= 1;
    }

    locations (5) {
        loc0:[0];
        loc1:[1];
        locAC:[2];
        locEC:[3];
        locRD:[4];
    }

    inits (6) {
        (loc0 + loc1) == (N - F);
        locAC == 0;
        locRD == 0;
        locEC == 0;
        nsntEC == 0;
        nsntRD == 0;
    }

    rules (10) {
        0: loc1 -> locEC
            when ( true )
            do { nsntEC' == nsntEC + 1 };
        1: loc0 -> locEC
            when ( (2 * nsntEC) >= (((N + T) + 1) - (2 * F)) )
            do { nsntEC' == nsntEC + 1 };
        2: loc0 -> locEC
            when ( nsntRD >= ((T + 1) - F) )
            do { nsntEC' == nsntEC + 1 };
        3: locEC -> locRD
            when ( (2 * nsntEC) >= (((N + T) + 1) - (2 * F)) )
            do { nsntRD' == nsntRD + 1 };
        4: locEC -> locRD
            when ( nsntRD >= ((T + 1) - F) )
            do { nsntRD' == nsntRD + 1 };
        5: locRD -> locAC
            when ( (2 * nsntRD) >= ((2 * T) + 1) )
            do {  };
        6: loc0 -> loc0
            when ( ((2 * nsntEC) < ((N + T) + 1) && nsntRD < (T + 1)) )
            do {  };
        7: locEC -> locEC
            when ( ((2 * nsntEC) < ((N + T) + 1) && nsntRD < (T + 1)) )
            do {  };
        8: locRD -> locRD
            when ( nsntRD < ((2 * T) + 1) )
            do {  };
        9: locAC -> locAC
            when ( true )
            do {  };
    }

    spec(3) {
    unforg: (loc1 == 0) -> ([](locAC == 0));
    corr: <>([](((((((((2 * nsntEC) < ((N + T) + 1)) || (loc0 == 0)) && ((nsntRD < (T + 1)) || (loc0 == 0))) && (((2 * nsntEC) < ((N + T) + 1)) || (locEC == 0))) && ((nsntRD < (T + 1)) || (locEC == 0))) && ((nsntRD < ((2 * T) + 1)) || (locRD == 0))) && (loc1 == 0)) -> ((loc0 == 0) -> (<>(locAC != 0)))));
    agreement: <>([](((((((((2 * nsntEC) < ((N + T) + 1)) || (loc0 == 0)) && ((nsntRD < (T + 1)) || (loc0 == 0))) && (((2 * nsntEC) < ((N + T) + 1)) || (locEC == 0))) && ((nsntRD < (T + 1)) || (locEC == 0))) && ((nsntRD < ((2 * T) + 1)) || (locRD == 0))) && (loc1 == 0)) -> ([]((locAC != 0) -> (<>((((loc0 == 0) && (loc1 == 0)) && (locEC == 0)) && (locRD == 0)))))));
    }
        
}";
        let (expected_ta, expected_ltl) = ByMCParser::new().parse_ta_and_spec(expected_ta).unwrap();

        assert_eq!(
            got_ta, expected_ta,
            "expected:\n{expected_ta}\n\ngot:\n{got_ta}"
        );
        assert_eq!(
            got_ta_2, expected_ta,
            "expected:\n{expected_ta}\n\ngot:\n{got_ta}"
        );
        assert_eq!(
            got_ltl, expected_ltl,
            "expected:\n{expected_ltl}\n\ngot:\n{got_ltl}"
        )
    }
}

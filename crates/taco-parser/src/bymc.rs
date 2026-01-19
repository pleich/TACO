//! This module contains the parser for the ByMC specification format.
//!
//! The parser uses the [pest](https://pest.rs/) parser generator, with the
//! grammar defined in `bymc_format.pest`. The grammar is based on the ByMC, but
//! allows for more flexibility in the specification.

use std::{collections::BTreeMap, fmt::Debug};

use anyhow::{Context, Error, anyhow};
use log::debug;
use pest::{
    Parser, Span, error,
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, PrattParser},
};
use pest_derive::Parser;
use taco_model_checker::eltl::{ELTLExpression, ELTLSpecification, ELTLSpecificationBuilder};

use taco_threshold_automaton::{
    expressions::{
        Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp,
        IsDeclared, Location, Parameter, Variable,
    },
    general_threshold_automaton::{
        Action, GeneralThresholdAutomaton,
        builder::{
            BuilderError, GeneralThresholdAutomatonBuilder,
            InitializedGeneralThresholdAutomatonBuilder, RuleBuilder,
        },
    },
};

use crate::ParseTAWithLTL;

use super::ParseTA;

// Location of the grammar file and generation of parser
#[allow(missing_docs)]
#[derive(Parser)]
#[grammar = "./bymc_format.pest"]
struct PestByMCParser;

// Pratt parser responsible for maintaining operator precedence
//
// Here we simply borrow them from C++
// [see](https://en.cppreference.com/w/cpp/language/operator_precedence)
//
// Additionally, we define the precedence of the temporal operators
// - `G` (Globally) and `F` (Eventually) have the highest precedence
// - `!` (Not) has the second highest precedence
lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Op};

        // Precedence is defined lowest to highest
        PrattParser::new()
            .op(Op::infix(Rule::or, Assoc::Left))
            .op(Op::infix(Rule::implication, Assoc::Right))
            .op(Op::infix(Rule::and, Assoc::Left))
            .op(Op::infix(Rule::equal, Assoc::Left) | Op::infix(Rule::n_equal, Assoc::Left))
            .op(Op::infix(Rule::less_eq, Assoc::Left)
                | Op::infix(Rule::less, Assoc::Left)
                | Op::infix(Rule::greater_eq, Assoc::Left)
                | Op::infix(Rule::greater, Assoc::Left))
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
            .op(Op::prefix(Rule::negation))
            .op(Op::prefix(Rule::not))
            .op(Op::prefix(Rule::eventually) |  Op::prefix(Rule::globally))
    };
}

/// Context to store the definitions of macros in
struct ByMCParsingContext<'a> {
    /// Macros for integer expressions
    define_macro: BTreeMap<String, Pair<'a, Rule>>,
}

impl<'a> ByMCParsingContext<'a> {
    fn new() -> Self {
        Self {
            define_macro: BTreeMap::new(),
        }
    }

    fn add_macro(
        &mut self,
        name: String,
        pair: Pair<'a, Rule>,
    ) -> Result<(), Box<pest::error::Error<()>>> {
        if self.define_macro.contains_key(&name) {
            return Err(new_parsing_error(
                format!("Duplicate macro with name '{}', second definition: ", name),
                pair.as_span(),
            ));
        }
        self.define_macro.insert(name, pair);
        Ok(())
    }
}

/// Parser for the ByMC format
///
/// This parser implements the `ParseToTA` trait and can be used to parse
/// threshold automata given in the ByMC format as introduced by
/// [BYMC](https://github.com/konnov/bymc).
pub struct ByMCParser;

impl ParseTA for ByMCParser {
    /// Parse a string in the ByMC to a threshold automaton
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_parser::bymc::ByMCParser;
    /// use crate::taco_parser::*;
    ///
    /// let spec = "skel Proc {
    ///     parameters n;
    ///     assumptions (1) {
    ///         n >= 0;
    ///     }
    ///     locations (0) {}
    ///     inits (0) {}
    ///     rules (0) {}
    /// }";
    /// let parser = ByMCParser::new();
    /// let ta = parser.parse_ta(spec).unwrap();
    /// ```
    fn parse_ta(&self, input: &str) -> Result<GeneralThresholdAutomaton, Error> {
        let (ta, _, _) = self.parse_ta_and_return_left_pair(input)?;
        Ok(ta)
    }
}

impl ParseTAWithLTL for ByMCParser {
    fn parse_ta_and_spec(
        &self,
        input: &str,
    ) -> Result<(GeneralThresholdAutomaton, ELTLSpecification), Error> {
        let (ta, mut pairs, ctx) = self.parse_ta_and_return_left_pair(input)?;

        let ltl_spec = Self::parse_specification_and_add_expressions(
            pairs
                .next()
                .ok_or_else(|| anyhow!("No specification found"))?,
            ELTLSpecificationBuilder::new(&ta),
            &ctx,
        )?;
        let ltl_spec = ltl_spec.build();

        Ok((ta, ltl_spec))
    }
}

impl Default for ByMCParser {
    fn default() -> Self {
        Self::new()
    }
}

impl ByMCParser {
    pub fn new() -> Self {
        ByMCParser {}
    }

    fn parse_ta_and_return_left_pair<'a>(
        &self,
        input: &'a str,
    ) -> Result<
        (
            GeneralThresholdAutomaton,
            Pairs<'a, Rule>,
            ByMCParsingContext<'a>,
        ),
        Error,
    > {
        let mut pairs = PestByMCParser::parse(Rule::bymc_spec, input)?;

        let pair = pairs.next().expect("Missing: name of threshold automaton");
        let name: String = parse_identifier_to_t(&pair);
        let mut builder = GeneralThresholdAutomatonBuilder::new(name);

        let error_msg_nxt_required = "Missing: parameters of threshold automaton";

        let mut pair = pairs.next().expect(error_msg_nxt_required);

        (builder, pair) =
            Self::handle_local_vars(&mut pairs, pair, builder, error_msg_nxt_required);

        (builder, pair) =
            Self::parse_shared_variables(&mut pairs, pair, builder, error_msg_nxt_required)
                .with_context(|| "Failed to parse shared variables:")?;

        (builder, pair) = Self::parse_and_add_parameters(&mut pairs, pair, builder)
            .with_context(|| "Failed to parse parameters: ")?;

        let mut ctx = ByMCParsingContext::new();
        (builder, pair) = Self::parse_and_add_define_macros(&mut pairs, pair, builder, &mut ctx)
            .with_context(|| "Failed to parse macro definitions: ")?;

        // Check for resilience conditions, delay the actual parsing after the builder initialization
        let mut rc = None;
        if pair.as_rule() == Rule::assumption_list {
            rc = Some(pair);
            pair = pairs
                .next()
                .expect("Missing: locations of threshold automaton");
        }

        (builder, pair) = Self::parse_and_add_locations(&mut pairs, pair, builder)
            .with_context(|| "Failed to parse locations: ")?;

        // Locations, Variables and Parameters are now fixed, initialize the builder
        let mut builder = builder.initialize();

        builder = Self::pares_and_add_potential_resilience_conditions(rc, builder, &ctx)?;

        (builder, pair) =
            Self::parse_and_add_location_and_var_constraints(&mut pairs, pair, builder, &ctx)?;

        builder = Self::parse_and_add_rules(pair, builder, &ctx)?;

        Ok((builder.build(), pairs, ctx))
    }

    /// Handle potential local variables of the threshold automaton and return next pair
    ///
    /// **NOTE**: Local variables are currently simply skipped
    fn handle_local_vars<'a>(
        pairs: &mut Pairs<'a, Rule>,
        mut pair: Pair<'a, Rule>,
        builder: GeneralThresholdAutomatonBuilder,
        err_msg: &str,
    ) -> (GeneralThresholdAutomatonBuilder, Pair<'a, Rule>) {
        while pair.as_rule() == Rule::local_variables {
            debug!("Local variables are not supported, skipping them!");
            pair = pairs.next().expect(err_msg);
        }

        (builder, pair)
    }

    /// Parse shared variables and add them to the builder
    ///
    /// This function checks whether the current pair is a shared variable list,
    /// parses the shared variable names and adds them to the builder.
    /// Afterwards, it computes the next pair to be processed.
    ///
    /// If that pair is a again a shared variable list, the function continues
    /// to parse until the next pair is not a shared variable list and returns
    /// that pair and the modified builder.
    fn parse_shared_variables<'a>(
        pairs: &mut Pairs<'a, Rule>,
        mut pair: Pair<'a, Rule>,
        mut builder: GeneralThresholdAutomatonBuilder,
        err_msg: &str,
    ) -> Result<(GeneralThresholdAutomatonBuilder, Pair<'a, Rule>), BuilderError> {
        while pair.as_rule() == Rule::shared_variables {
            let vars = parse_identifier_list_to_t::<Variable>(pair.into_inner().next().unwrap());
            builder = builder.with_variables(vars)?;

            pair = pairs.next().expect(err_msg);
        }

        Ok((builder, pair))
    }

    /// Parse the list of parameters and add them to the builder
    ///
    /// A parameter list must exist by the grammar definition.
    fn parse_and_add_parameters<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: GeneralThresholdAutomatonBuilder,
    ) -> Result<(GeneralThresholdAutomatonBuilder, Pair<'a, Rule>), BuilderError> {
        debug_assert!(
            pair.as_rule() == Rule::parameters,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str(),
        );

        let mut pair = pair;
        let mut builder = builder;

        while pair.as_rule() == Rule::parameters {
            let parameters =
                parse_identifier_list_to_t::<Parameter>(pair.into_inner().next().unwrap());

            builder = builder.with_parameters(parameters)?;

            pair = pairs
                .next()
                .expect("Missing: locations of threshold automaton");
        }

        Ok((builder, pair))
    }

    fn parse_and_add_define_macros<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        builder: GeneralThresholdAutomatonBuilder,
        ctx: &mut ByMCParsingContext<'a>,
    ) -> Result<(GeneralThresholdAutomatonBuilder, Pair<'a, Rule>), Box<pest::error::Error<()>>>
    {
        let mut pair = pair;
        while pair.as_rule() == Rule::define_statement {
            let mut inners = pair.into_inner();

            let ident_pair = inners.next().expect("Missing: define identifier");
            let ident: String = parse_identifier_to_t(&ident_pair);

            let int_pair = inners.next().expect("Missing: define integer expr");
            ctx.add_macro(ident, int_pair)?;

            pair = pairs.next().expect("Missing: location definition");
        }
        Ok((builder, pair))
    }

    /// Parse the list of locations and add them to the builder
    ///
    /// A location list must exist by the grammar definition.
    fn parse_and_add_locations<'a>(
        pairs: &mut Pairs<'a, Rule>,
        pair: Pair<'a, Rule>,
        mut builder: GeneralThresholdAutomatonBuilder,
    ) -> Result<(GeneralThresholdAutomatonBuilder, Pair<'a, Rule>), BuilderError> {
        debug_assert!(
            pair.as_rule() == Rule::location_list,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str(),
        );

        let locations = parse_location_list(pair);
        builder = builder.with_locations(locations)?;

        let pair = pairs.next().expect("Missing: rules of threshold automaton");

        Ok((builder, pair))
    }

    /// Parse potential resilience conditions and add them to the builder
    ///
    /// This function checks whether the current pair is a resilience condition
    /// list, if so it tries to parse the resilience conditions and adds them
    /// to the builder.
    fn pares_and_add_potential_resilience_conditions(
        pair: Option<Pair<'_, Rule>>,
        mut builder: InitializedGeneralThresholdAutomatonBuilder,
        ctx: &ByMCParsingContext,
    ) -> Result<InitializedGeneralThresholdAutomatonBuilder, anyhow::Error> {
        if let Some(pair) = pair {
            debug_assert!(
                pair.as_rule() == Rule::assumption_list,
                "Got rule {:?} for {}",
                pair.as_rule(),
                pair.as_str(),
            );

            let mut pairs = pair.into_inner();

            // integer specifying the number of assumptions, ignoring since it is usually invalid
            let _n_rc = parse_integer_const(pairs.next().unwrap());

            let rc = parse_boolean_expr_list(pairs.next().unwrap(), &builder, ctx)
                .with_context(|| "Failed to parse resilience conditions (assumptions):")?;

            builder = builder
                .with_resilience_conditions(rc)
                .with_context(|| "Failed to validate resilience conditions (assumptions): ")?;
        }

        Ok(builder)
    }

    /// Parse potential location constraints and add them to the builder
    ///
    /// This function checks whether the current pair specifies initial
    /// constraints. It then tries to parse it into a variable constraint. If
    /// the constraint is not accepted by the initialized builder, it tries to
    /// parse it into a location constraint and returns the result.
    fn parse_and_add_location_and_var_constraints<'a>(
        pairs: &mut Pairs<'a, Rule>,
        mut pair: Pair<'a, Rule>,
        mut builder: InitializedGeneralThresholdAutomatonBuilder,
        ctx: &ByMCParsingContext,
    ) -> Result<(InitializedGeneralThresholdAutomatonBuilder, Pair<'a, Rule>), anyhow::Error> {
        if pair.as_rule() == Rule::initial_condition_list {
            let mut inner_pairs = pair.into_inner();

            // integer specifying the number of constraints, ignoring since it is usually invalid
            let _n_loc_constr = parse_integer_const(inner_pairs.next().unwrap());

            let inner_pair = inner_pairs
                .next()
                .expect("Missing: initial location / variable constraints (inits)");
            debug_assert!(
                inner_pair.as_rule() == Rule::boolean_expr_list,
                "Got rule {:?} for {}",
                inner_pair.as_rule(),
                inner_pair.as_str(),
            );
            inner_pairs = inner_pair.into_inner();

            for init_cond in inner_pairs {
                let span = init_cond.as_span();
                let var_cond: Result<BooleanExpression<Variable>, _> =
                    parse_boolean_expr(init_cond.clone(), &builder, ctx);

                if let Ok(var_cond) = var_cond {
                    builder = builder
                        .with_initial_variable_constraint(var_cond)
                        .with_context(
                            || "Failed to validate initial variable constraint (inits): ",
                        )?;
                    continue;
                }

                let loc_constraint: BooleanExpression<Location> =
                    parse_boolean_expr(init_cond, &builder, ctx)
                        .map_err(|err| {
                            new_parsing_error(format!("Unknown identifier: {err}"), span)
                        })
                        .with_context(
                            || "Failed to parse initial location / variable constraints (inits): ",
                        )?;

                builder = builder
                    .with_initial_location_constraint(loc_constraint)
                    .with_context(
                        || "Failed to validate initial location / variable constraints (inits): ",
                    )?;
            }

            pair = pairs
                .next()
                .expect("Missing: rules of the threshold automaton");
        }

        Ok((builder, pair))
    }

    /// Parse the list of rules and add them to the builder
    fn parse_and_add_rules(
        pair: Pair<'_, Rule>,
        builder: InitializedGeneralThresholdAutomatonBuilder,
        ctx: &ByMCParsingContext,
    ) -> Result<InitializedGeneralThresholdAutomatonBuilder, anyhow::Error> {
        debug_assert!(
            pair.as_rule() == Rule::rule_list,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str()
        );

        let mut pairs = pair.into_inner();

        // integer specifying the number of rules, ignoring since it is usually invalid
        let _n_rules = parse_integer_const(pairs.next().unwrap());

        let rules = pairs
            .map(|r| parse_rule(r, &builder, ctx))
            .collect::<Result<Vec<_>, _>>()
            .with_context(|| "Failed to parse rules: ")?;

        builder
            .with_rules(rules)
            .with_context(|| "Failed to parse rules: ")
    }

    /// Parse specification list into ltl expressions
    fn parse_specification_and_add_expressions<'a>(
        pair: Pair<'_, Rule>,
        mut builder: ELTLSpecificationBuilder<'a, GeneralThresholdAutomaton>,
        ctx: &ByMCParsingContext,
    ) -> Result<ELTLSpecificationBuilder<'a, GeneralThresholdAutomaton>, anyhow::Error> {
        debug_assert!(
            pair.as_rule() == Rule::specification_list,
            "Got rule {:?} for {}",
            pair.as_rule(),
            pair.as_str()
        );

        let mut pairs = pair.into_inner();

        // integer specifying the number of rules, ignoring since it is usually invalid
        let _n_specs = parse_integer_const(pairs.next().unwrap());

        let expressions = pairs
            .map(|spec| parse_ltl_specification(spec, &builder, ctx))
            .collect::<Result<Vec<_>, Error>>()
            .with_context(|| "Failed to parse specifications: ")?;

        builder
            .add_expressions(expressions)
            .with_context(|| "Specification failed validation: ")?;
        Ok(builder)
    }
}

/// Parse a single ltl specification
///
/// This function parses a single ltl specification and returns the name of the
/// specification and the ltl expression.
fn parse_ltl_specification<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<(String, ELTLExpression), Error>
where
    T: IsDeclared<Variable> + IsDeclared<Location> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::specification,
        "Expected a specification, got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let mut pairs = pair.into_inner();

    let name: String = parse_identifier_to_t(&pairs.next().unwrap());

    let expression = parse_ltl_expr(pairs.next().unwrap(), builder, ctx)?;

    Ok((name, expression))
}

/// Parse an ltl expression into a single ltl expression
///
/// This function parses an ltl expression with operator precedence
/// and returns the corresponding ltl expression.
/// The function returns an error if the expression refers to an unknown location.
fn parse_ltl_expr<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<ELTLExpression, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Location> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::ltl_expr,
        "Expected an LTL expression, got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pairs = pair.into_inner();
    PRATT_PARSER
        .map_primary(|atom| parse_ltl_atom(atom, builder, ctx))
        .map_infix(|lhs, op, rhs| {
            let lhs = lhs?;
            let rhs = rhs?;

            let op = match op.as_rule() {
                Rule::and => ELTLExpression::And(Box::new(lhs), Box::new(rhs)),
                Rule::or => ELTLExpression::Or(Box::new(lhs), Box::new(rhs)),
                Rule::implication => ELTLExpression::Implies(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(
                    "Unknown rule for binary ltl operator {:?}: {}",
                    op.as_rule(),
                    op.as_str()
                ),
            };

            Ok(op)
        })
        .map_prefix(|op, rhs| {
            let rhs = rhs?;

            match op.as_rule() {
                Rule::not => Ok(ELTLExpression::Not(Box::new(rhs))),
                Rule::globally => Ok(ELTLExpression::Globally(Box::new(rhs))),
                Rule::eventually => Ok(ELTLExpression::Eventually(Box::new(rhs))),
                _ => unreachable!(
                    "Unknown rule for unary ltl operator {:?}: {}",
                    op.as_rule(),
                    op.as_str()
                ),
            }
        })
        .parse(pairs)
}

/// Parse an ltl atom into a single ltl expression
///
/// This function parses an ltl atom and returns the corresponding ltl expression.
/// The function returns an error if the expression refers to an unknown location.
fn parse_ltl_atom<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<ELTLExpression, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Location> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::ltl_atom,
        "Expected an LTL atom, got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();

    match pair.as_rule() {
        Rule::ltl_expr => parse_ltl_expr(pair, builder, ctx),
        Rule::ltl_unary_op => {
            let op = pair.into_inner().next().unwrap();
            let expr = pairs
                .next()
                .expect("Missing LTL expression after unary operator");
            let expr = parse_ltl_atom(expr, builder, ctx)?;

            match op.as_rule() {
                Rule::not => Ok(ELTLExpression::Not(Box::new(expr))),
                Rule::globally => Ok(ELTLExpression::Globally(Box::new(expr))),
                Rule::eventually => Ok(ELTLExpression::Eventually(Box::new(expr))),
                _ => unreachable!(
                    "Unknown rule for unary operator {:?}: {}",
                    op.as_rule(),
                    op.as_str()
                ),
            }
        }
        Rule::comparison_expr => {
            let span = pair.as_span();

            // First: attempt to parse parameter expression !
            // This is important as constraints purely on parameters are also
            // valid for variable / location expressions
            if let Ok((lhs, op, rhs)) =
                parse_comparison_expr::<Parameter, T>(pair.clone(), builder, ctx)
            {
                return Ok(ELTLExpression::ParameterExpr(
                    Box::new(lhs),
                    op,
                    Box::new(rhs),
                ));
            }

            if let Ok((lhs, op, rhs)) =
                parse_comparison_expr::<Variable, T>(pair.clone(), builder, ctx)
            {
                return Ok(ELTLExpression::VariableExpr(
                    Box::new(lhs),
                    op,
                    Box::new(rhs),
                ));
            }

            let (lhs, op, rhs) = parse_comparison_expr(pair, builder, ctx).map_err(|_err| {
                new_parsing_error("Failed to parse inner ltl expression. This is most likely due to an unknown identifier".to_string(), span)
            })?;
            let expr = ELTLExpression::LocationExpr(Box::new(lhs), op, Box::new(rhs));
            Ok(expr)
        }
        Rule::bool_const => {
            let pair = pair.into_inner().next().unwrap();

            match pair.as_rule() {
                Rule::bool_true => Ok(ELTLExpression::True),
                Rule::bool_false => Ok(ELTLExpression::False),
                _ => unreachable!(
                    "Unknown rule for boolean constant {:?}: {}",
                    pair.as_rule(),
                    pair.as_str()
                ),
            }
        }
        _ => unreachable!(
            "Unknown rule for ltl atom {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

/// Parse a location definition
#[inline(always)]
fn parse_location(pair: Pair<'_, Rule>) -> Location {
    debug_assert!(
        pair.as_rule() == Rule::location,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let id_pair = pair.into_inner().next().unwrap();

    parse_identifier_to_t(&id_pair)

    // ignoring integer(s) here, does not seem to have a semantic
}

/// Parse a list of location definitions
fn parse_location_list(pair: Pair<'_, Rule>) -> Vec<Location> {
    debug_assert!(
        pair.as_rule() == Rule::location_list,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let mut pairs = pair.into_inner();

    let n_locs = parse_integer_const(pairs.next().unwrap());

    let locs = pairs.map(|loc| parse_location(loc)).collect::<Vec<_>>();

    if n_locs != locs.len().try_into().unwrap() {
        debug!(
            "Specified number of locations {} does not match found number of locations {}",
            n_locs,
            locs.len()
        )
    }

    locs
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

/// Parse a list of identifiers into a vector of objects of type T
#[inline(always)]
fn parse_identifier_list_to_t<T: for<'a> From<&'a str>>(
    pair: Pair<'_, Rule>,
) -> impl Iterator<Item = T> {
    debug_assert!(
        pair.as_rule() == Rule::identifier_list,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    pair.into_inner().map(|id| parse_identifier_to_t::<T>(&id))
}

/// Parse a reset expression into the corresponding list of actions
fn parse_reset_expression(pair: Pair<'_, Rule>) -> Vec<Action> {
    debug_assert!(
        pair.as_rule() == Rule::reset_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    parse_identifier_list_to_t::<Variable>(pair.into_inner().next().unwrap())
        .map(Action::new_reset)
        .collect()
}

/// Parse an assignment expression of an action into the corresponding list of actions
fn parse_assignment_expression<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<Action, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::assignment_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    let span = pair.as_span();

    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();

    let var = parse_identifier_to_t(&pair);
    if !builder.is_declared(&var) {
        return Err(new_parsing_error(
            format!("Failed to parse action: Unknown identifier: {var}"),
            span,
        ));
    }

    let expr = parse_integer_expr(pairs.next().unwrap(), builder, ctx)
        .map_err(|err| new_parsing_error(format!("Failed to parse action: {err}"), span))?;

    Action::new(var, expr)
        .map_err(|err| new_parsing_error(format!("Failed to parse effect of action: {err}"), span))
}

/// Parse an action expression into a list of actions
fn parse_action_expr<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<Vec<Action>, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::action_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pair = pair.into_inner().next().unwrap();

    Ok(match pair.as_rule() {
        Rule::unchanged_expr => vec![],
        Rule::reset_expr => parse_reset_expression(pair),
        Rule::assignment_expr => vec![parse_assignment_expression(pair, builder, ctx)?],
        _ => unreachable!(
            "Unknown rule for action expression {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    })
}

/// Parse a list of action expressions into a combined list of actions
#[inline(always)]
fn parse_action_list<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<Vec<Action>, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::action_list,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    pair.into_inner()
        .map(|action| parse_action_expr(action, builder, ctx))
        .try_fold(vec![], |mut acc, x| {
            acc.append(&mut x?);
            Ok(acc)
        })
}

/// Parse integer constant
#[inline(always)]
fn parse_integer_const(pair: Pair<'_, Rule>) -> u32 {
    debug_assert!(
        pair.as_rule() == Rule::integer_const,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    pair.as_str().parse::<u32>().unwrap()
}

/// Parse an integer operator
#[inline(always)]
fn parse_integer_binary_op(pair: Pair<'_, Rule>) -> IntegerOp {
    match pair.as_rule() {
        Rule::add => IntegerOp::Add,
        Rule::sub => IntegerOp::Sub,
        Rule::mul => IntegerOp::Mul,
        Rule::div => IntegerOp::Div,
        _ => unreachable!(
            "Unknown rule for operator {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

/// Parse integer atom
///
/// Returns an integer expression if the pair is a constant, known identifier,
/// or  could be parsed to an expression
/// Returns an error if the identifier was not declared with the identifier name
fn parse_integer_atom<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &ByMCParsingContext,
) -> Result<IntegerExpression<T>, String>
where
    T: Atomic,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::integer_atom,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::integer_const => Ok(IntegerExpression::Const(parse_integer_const(pair))),
        Rule::identifier => {
            let ident: String = parse_identifier_to_t(&pair);
            if ctx.define_macro.contains_key(&ident) {
                return parse_integer_expr(ctx.define_macro[&ident].clone(), builder, ctx);
            }

            let atom = parse_identifier_to_t(&pair);
            if builder.is_declared(&atom) {
                return Ok(IntegerExpression::Atom(atom));
            }

            let param = parse_identifier_to_t(&pair);
            if builder.is_declared(&param) {
                return Ok(IntegerExpression::Param(param));
            }

            Err(format!("Unknown identifier: {}", pair.as_str()))
        }
        Rule::integer_expr => parse_integer_expr(pair, builder, ctx),
        _ => unreachable!(
            "Unknown integer atom {:#?} : {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

/// Parse expression over integers into an integer expression
fn parse_integer_expr<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &ByMCParsingContext,
) -> Result<IntegerExpression<T>, String>
where
    T: Atomic,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::integer_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );
    let pairs = pair.into_inner();

    PRATT_PARSER
        .map_primary(|atom| parse_integer_atom(atom, builder, ctx))
        .map_infix(|lhs, op, rhs| {
            let op = parse_integer_binary_op(op);

            Ok(IntegerExpression::BinaryExpr(
                Box::new(lhs?),
                op,
                Box::new(rhs?),
            ))
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::negation => Ok(IntegerExpression::Neg(Box::new(rhs?))),
            _ => unreachable!(
                "Unknown integer unary operator {:?}: {}",
                op.as_rule(),
                op.as_str()
            ),
        })
        .parse(pairs)
}

/// Parse boolean constant
#[inline(always)]
fn parse_boolean_const<T: Atomic>(pair: Pair<'_, Rule>) -> BooleanExpression<T> {
    debug_assert!(
        pair.as_rule() == Rule::bool_const,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pair = pair
        .into_inner()
        .next()
        .expect("Expected boolean constant to be non-empty");

    match pair.as_rule() {
        Rule::bool_true => BooleanExpression::True,
        Rule::bool_false => BooleanExpression::False,
        _ => unreachable!(
            "Unexpected rule for boolean constant {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

/// Parse boolean connectives
#[inline(always)]
fn parse_boolean_con(pair: Pair<'_, Rule>) -> BooleanConnective {
    match pair.as_rule() {
        Rule::and => BooleanConnective::And,
        Rule::or => BooleanConnective::Or,
        _ => unreachable!(
            "Unknown rule for boolean connective {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

/// Parse comparison operator
#[inline(always)]
fn parse_comparison_op(pair: Pair<'_, Rule>) -> ComparisonOp {
    match pair.as_rule() {
        Rule::equal => ComparisonOp::Eq,
        Rule::n_equal => ComparisonOp::Neq,
        Rule::less_eq => ComparisonOp::Leq,
        Rule::less => ComparisonOp::Lt,
        Rule::greater_eq => ComparisonOp::Geq,
        Rule::greater => ComparisonOp::Gt,
        _ => unreachable!(
            "Unknown rule for comparison operator {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

/// Intermediate type for comparison expression of the form `lhs op rhs`
type CompExpr<T> = (IntegerExpression<T>, ComparisonOp, IntegerExpression<T>);

/// Parse comparison expression, relating two integer expressions
fn parse_comparison_expr<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &ByMCParsingContext,
) -> Result<CompExpr<T>, String>
where
    T: Atomic,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::comparison_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let mut pairs = pair.into_inner();

    let lhs = parse_integer_expr(pairs.next().unwrap(), builder, ctx)?;
    let op = parse_comparison_op(pairs.next().unwrap());
    let rhs = parse_integer_expr(pairs.next().unwrap(), builder, ctx)?;

    Ok((lhs, op, rhs))
}

/// Parse a constraint from a boolean expression
fn parse_boolean_expr<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &ByMCParsingContext,
) -> Result<BooleanExpression<T>, String>
where
    T: Atomic,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::boolean_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pairs = pair.into_inner();

    // utilize the precedence parser
    PRATT_PARSER
        .map_primary(|atom| parse_boolean_atom(atom, builder, ctx))
        .map_infix(|lhs, op, rhs| {
            let op = parse_boolean_con(op);

            Ok(BooleanExpression::BinaryExpression(
                Box::new(lhs?),
                op,
                Box::new(rhs?),
            ))
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::not => Ok(BooleanExpression::Not(Box::new(rhs?))),
            _ => unreachable!(
                "Unknown boolean unary operator {:?}: {}",
                op.as_rule(),
                op.as_str()
            ),
        })
        .parse(pairs)
}

/// Parse boolean_atom
#[inline(always)]
fn parse_boolean_atom<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &ByMCParsingContext,
) -> Result<BooleanExpression<T>, String>
where
    T: Atomic,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::boolean_atom,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pair = pair
        .into_inner()
        .next()
        .expect("Expected boolean atom to be non-empty");

    match pair.as_rule() {
        Rule::bool_const => Ok(parse_boolean_const(pair)),
        Rule::boolean_expr => parse_boolean_expr(pair, builder, ctx),
        Rule::comparison_expr => {
            let (lhs, op, rhs) = parse_comparison_expr(pair, builder, ctx)?;
            Ok(BooleanExpression::ComparisonExpression(
                Box::new(lhs),
                op,
                Box::new(rhs),
            ))
        }
        _ => unreachable!(
            "Unknown rule for boolean atom {:?}: {}",
            pair.as_rule(),
            pair.as_str(),
        ),
    }
}

/// Parse list of boolean expressions
#[inline(always)]
fn parse_boolean_expr_list<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &ByMCParsingContext,
) -> Result<Vec<BooleanExpression<T>>, Box<pest::error::Error<()>>>
where
    T: Atomic,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::boolean_expr_list,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    pair.into_inner()
        .map(|expr| {
            let span = expr.as_span();

            parse_boolean_expr(expr, builder, ctx).map_err(|err| new_parsing_error(err, span))
        })
        .collect()
}

/// Parse a rule
fn parse_rule<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &ByMCParsingContext,
) -> Result<taco_threshold_automaton::general_threshold_automaton::Rule, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Parameter> + IsDeclared<Location>,
{
    debug_assert!(
        pair.as_rule() == Rule::rule,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let mut pairs = pair.into_inner();

    let id = parse_integer_const(pairs.next().unwrap());

    let pair = pairs.next().unwrap();
    let source: Location = parse_identifier_to_t(&pair);

    let pair = pairs.next().unwrap();
    let target: Location = parse_identifier_to_t(&pair);

    let mut rule_builder = RuleBuilder::new(id, source, target);

    let pair = pairs.next().unwrap();
    let span = pair.as_span();

    let guard = parse_boolean_expr(pair, builder, ctx).map_err(|err| {
        new_parsing_error(format!("Failed to parse guard of rule {id}: {err}"), span)
    })?;

    rule_builder = rule_builder.with_guard(guard);

    let actions = parse_action_list(pairs.next().unwrap(), builder, ctx)?;
    rule_builder = rule_builder.with_actions(actions);

    Ok(rule_builder.build())
}

/// Generate a new parsing error
#[inline(always)]
fn new_parsing_error(message: String, span: Span<'_>) -> Box<pest::error::Error<()>> {
    Box::new(error::Error::new_from_span(
        error::ErrorVariant::CustomError { message },
        span,
    ))
}

#[cfg(test)]
mod test {
    use super::*;

    // These tests do test private functions that are not exposed to a user, but they have been useful for debugging
    // and are kept for now.
    mod simple_parse_funcs {
        use super::*;

        macro_rules! parse_func_test
         {
            ($name:ident, $($test_spec:expr, $expected_out:expr, $rule:expr, $parse_func:expr),+) => {
                #[test]
                fn $name() {
                    $(
                        let test_spec = $test_spec;
                        let mut parsed_pairs = PestByMCParser::parse($rule, test_spec).unwrap();
                        let exp_pair = parsed_pairs.next().unwrap();
                        let ctx = ByMCParsingContext::new();

                        let builder = GeneralThresholdAutomatonBuilder::new("test_ta")
                                        .with_parameters(vec![Parameter::new("n"), Parameter::new("f")])
                                        .unwrap()
                                        .with_variables(vec![Variable::new("x"), Variable::new("y"), Variable::new("var1"), Variable::new("var2"), Variable::new("var3")])
                                        .unwrap()
                                        .with_locations(vec![Location::new("loc"), Location::new("loc1"), Location::new("loc2")])
                                        .unwrap()
                                        .initialize();

                        let got_expr = $parse_func(exp_pair, &builder, &ctx);
                        let got_expr = got_expr.unwrap();

                        assert_eq!(got_expr, $expected_out);

                        assert!(parsed_pairs.next().is_none(), "Found more tokens: {:#?}", parsed_pairs);
                    )*
                }

            };
        }

        #[test]
        fn test_parse_identifier_list_to_string() {
            let test_spec = "a, b, c, abcdefg, gg, __gg, gg32";
            let mut parsed_pairs = PestByMCParser::parse(Rule::identifier_list, test_spec).unwrap();
            let pair = parsed_pairs.next().unwrap();

            let got_expr: Vec<String> = parse_identifier_list_to_t(pair).collect();

            let expected_expr = vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
                "abcdefg".to_string(),
                "gg".to_string(),
                "__gg".to_string(),
                "gg32".to_string(),
            ];

            assert_eq!(got_expr, expected_expr);

            assert!(
                parsed_pairs.next().is_none(),
                "Found more tokens: {parsed_pairs:#?}"
            );
        }

        #[test]
        fn parse_location_list_test() {
            let test_spec = "locations (3) {
                loc1 : [0];
                loc2 : [1];
                loc3 : [2];
            }
            ";

            let expected_locs = vec![
                Location::new("loc1"),
                Location::new("loc2"),
                Location::new("loc3"),
            ];

            print!(
                "{:#?}",
                PestByMCParser::parse(Rule::location_list, test_spec).err()
            );

            let mut parsed_pairs = PestByMCParser::parse(Rule::location_list, test_spec).unwrap();
            let pair = parsed_pairs.next().unwrap();

            let got_locs = parse_location_list(pair);

            assert_eq!(expected_locs, got_locs);

            assert!(
                parsed_pairs.next().is_none(),
                "Found more tokens: {parsed_pairs:#?}"
            );
        }

        parse_func_test!(
            parse_action_expr_reset,
            "reset(x, y, z)",
            vec![
                Action::new_reset(Variable::new("x")),
                Action::new_reset(Variable::new("y")),
                Action::new_reset(Variable::new("z")),
            ],
            Rule::action_expr,
            parse_action_expr
        );

        parse_func_test!(
            parse_action_expr_increment,
            "x' := x + 1",
            vec![
                Action::new(
                    Variable::new("x"),
                    IntegerExpression::Atom(Variable::new("x")) + IntegerExpression::Const(1),
                )
                .unwrap()
            ],
            Rule::action_expr,
            parse_action_expr
        );

        parse_func_test!(
            parse_action_expr_unchanged,
            "unchanged(x, y, z)",
            Vec::<Action>::new(),
            Rule::action_expr,
            parse_action_expr
        );

        parse_func_test!(
            parse_action_list_mixed,
            "reset(a,b,c); x' := x + 1, unchanged(p,q)",
            vec![
                Action::new_reset(Variable::new("a")),
                Action::new_reset(Variable::new("b")),
                Action::new_reset(Variable::new("c")),
                Action::new(
                    Variable::new("x"),
                    IntegerExpression::Atom(Variable::new("x")) + IntegerExpression::Const(1),
                )
                .unwrap(),
            ],
            Rule::action_list,
            parse_action_list
        );

        parse_func_test!(
            parse_integer_expr_const,
            "5",
            IntegerExpression::<Location>::Const(5),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_expr_location,
            "loc",
            IntegerExpression::<Location>::Atom(Location::new("loc")),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_expr_parameter,
            "n",
            IntegerExpression::<Location>::Param(Parameter::new("n")),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_expr_add,
            "5 + 5",
            IntegerExpression::<Location>::BinaryExpr(
                Box::new(IntegerExpression::Const(5)),
                IntegerOp::Add,
                Box::new(IntegerExpression::Const(5)),
            ),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_operator_precedence_1,
            "5 + 5 * 5",
            IntegerExpression::<Parameter>::BinaryExpr(
                Box::new(IntegerExpression::Const(5)),
                IntegerOp::Add,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(5)),
                    IntegerOp::Mul,
                    Box::new(IntegerExpression::Const(5)),
                )),
            ),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_operator_precedence_2,
            "5 / 5 - 5",
            IntegerExpression::<Variable>::BinaryExpr(
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(5)),
                    IntegerOp::Div,
                    Box::new(IntegerExpression::Const(5)),
                )),
                IntegerOp::Sub,
                Box::new(IntegerExpression::Const(5)),
            ),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_un_op,
            "-3",
            IntegerExpression::<Location>::Neg(Box::new(IntegerExpression::Const(3))),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_integer_mixed,
            "-3 + n - loc",
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::<Location>::Neg(Box::new(
                        IntegerExpression::Const(3)
                    ))),
                    IntegerOp::Add,
                    Box::new(IntegerExpression::Param(Parameter::new("n")))
                )),
                IntegerOp::Sub,
                Box::new(IntegerExpression::Atom(Location::new("loc")))
            ),
            Rule::integer_expr,
            parse_integer_expr
        );

        parse_func_test!(
            parse_boolean_const_true,
            "true",
            BooleanExpression::<Location>::True,
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_boolean_const_true1,
            "1",
            BooleanExpression::<Location>::True,
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_boolean_const_false,
            "false",
            BooleanExpression::<Location>::False,
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_boolean_comp_op_1,
            "x > 1",
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ),
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_boolean_comp_op_2,
            "x <= 1",
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Leq,
                Box::new(IntegerExpression::Const(1)),
            ),
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_boolean_comp_op_negated,
            "!(x > 1)",
            BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ))),
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_boolean_comp_op_complex,
            "var2 >=  1 && var2 < 1 || var3 != n",
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1)),
                    )),
                    BooleanConnective::And,
                    Box::new(BooleanExpression::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(1)),
                    ))
                )),
                BooleanConnective::Or,
                Box::new(BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("var3"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ))
            ),
            Rule::boolean_expr,
            parse_boolean_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_globally,
            "[](loc1 == 0 -> loc2 == 1)",
            ELTLExpression::Globally(Box::new(ELTLExpression::Implies(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0))
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1))
                )),
            ))),
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_const,
            "0 == 0",
            ELTLExpression::ParameterExpr(
                Box::new(IntegerExpression::Const(0)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0))
            ),
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_true,
            "true",
            ELTLExpression::True,
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_false,
            "false",
            ELTLExpression::False,
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_adv_globally,
            "[](loc1 == 0 -> loc2 == 1 + 3)",
            ELTLExpression::Globally(Box::new(ELTLExpression::Implies(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0))
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1) + IntegerExpression::Const(3))
                )),
            ))),
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_eventually,
            "<>(loc1 == n -> !loc2 == 1)",
            ELTLExpression::Eventually(Box::new(ELTLExpression::Implies(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Param(Parameter::new("n")))
                )),
                Box::new(ELTLExpression::Not(Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1))
                )))),
            ))),
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_and,
            "[](loc1 == 0 -> loc2 == 1) && <>(loc1 == n -> !loc2 == 1)",
            ELTLExpression::And(
                Box::new(ELTLExpression::Globally(Box::new(ELTLExpression::Implies(
                    Box::new(ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0))
                    )),
                    Box::new(ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1))
                    )),
                )))),
                Box::new(ELTLExpression::Eventually(Box::new(
                    ELTLExpression::Implies(
                        Box::new(ELTLExpression::LocationExpr(
                            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n")))
                        )),
                        Box::new(ELTLExpression::Not(Box::new(ELTLExpression::LocationExpr(
                            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1))
                        )))),
                    )
                )))
            ),
            Rule::ltl_expr,
            parse_ltl_expr
        );

        parse_func_test!(
            parse_ltl_expr_simple_or,
            "[](loc1 == 0 -> loc2 == 1) || <>(loc1 == n -> !loc2 == 1)",
            ELTLExpression::Or(
                Box::new(ELTLExpression::Globally(Box::new(ELTLExpression::Implies(
                    Box::new(ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0))
                    )),
                    Box::new(ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1))
                    )),
                )))),
                Box::new(ELTLExpression::Eventually(Box::new(
                    ELTLExpression::Implies(
                        Box::new(ELTLExpression::LocationExpr(
                            Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Param(Parameter::new("n")))
                        )),
                        Box::new(ELTLExpression::Not(Box::new(ELTLExpression::LocationExpr(
                            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(1))
                        )))),
                    )
                )))
            ),
            Rule::ltl_expr,
            parse_ltl_expr
        );

        // Check that parameter constraints are parsed as parameter expressions
        parse_func_test!(
            parse_ltl_expr_param_as_variable_expr,
            "n == 0",
            ELTLExpression::ParameterExpr(
                Box::new(IntegerExpression::Atom(Parameter::new("n"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0))
            ),
            Rule::ltl_expr,
            parse_ltl_expr
        );
    }

    mod full_spec {
        use taco_threshold_automaton::{
            BooleanVarConstraint, LocationConstraint, ParameterConstraint,
        };

        use super::*;

        #[test]
        fn test_parse_skeleton_spec() {
            let test_spec = "
            skel Proc {
                parameters n;

                assumptions (1) {
                    n >= 0;
                }

                locations (2) {
                }

                inits (3) {
                }

                rules (4) {
                }

                specifications (0) {
                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("Proc")
                .with_parameter(Parameter::new("n"))
                .unwrap()
                .initialize()
                .with_resilience_condition(BooleanExpression::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(0)),
                ))
                .unwrap()
                .build();

            let parser = ByMCParser::new();
            let (got_ta, got_spec) = parser.parse_ta_and_spec(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta);

            let expected_spec = ELTLSpecificationBuilder::new(&got_ta).build();

            assert_eq!(got_spec, expected_spec);
        }

        #[test]
        fn test_parse_ta_1() {
            let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == n - f  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 == 1 && var2 == n)
                        do { reset(var3); var1' == var1 + 1  };
                }

                specifications (1) {
                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                ])
                .unwrap()
                .with_variables(vec![
                    Variable::new("var1"),
                    Variable::new("var2"),
                    Variable::new("var3"),
                ])
                .unwrap()
                .with_locations(vec![
                    Location::new("loc1"),
                    Location::new("loc2"),
                    Location::new("loc3"),
                ])
                .unwrap()
                .initialize()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                    RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                        .with_guard(BooleanExpression::BinaryExpression(
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Const(1)),
                            )),
                            BooleanConnective::And,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            )),
                        ))
                        .with_action(Action::new_reset(Variable::new("var3")))
                        .with_action(
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::Atom(Variable::new("var1"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                ])
                .unwrap()
                .with_initial_location_constraint(LocationConstraint::BinaryExpression(
                    Box::new(LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            IntegerOp::Sub,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    )),
                    BooleanConnective::Or,
                    Box::new(LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    )),
                ))
                .unwrap()
                .with_initial_variable_constraints(vec![
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var3"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(3)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Param(Parameter::new("f"))),
                    )),
                ))
                .unwrap()
                .build();

            let parser = ByMCParser;
            let got_ta = parser.parse_ta(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta)
        }

        #[test]
        fn test_parse_ta_1_with_define() {
            let test_spec = "
            skel test_ta1 {
                shared var1, var2, var3;
                parameters n, t, f;
                
                define THRESH_1 == n-f;
                define THRESH_2 == n;

                assumptions (1) {
                    n > 3 * f;
                }

                locations (2) {
                    loc1 : [0];
                    loc2 : [1];
                    loc3 : [2];
                }

                inits (1) {
                    loc1 == THRESH_1  || loc2 == 0;
                    var1 == 0;
                    var2 == 0;
                    var3 == 0;
                }

                rules (4) {
                    0: loc1 -> loc2
                        when(true)
                        do {};
                    1: loc2 -> loc3
                        when( var1 == 1 && var2 == THRESH_2)
                        do { reset(var3); var1' == var1 + 1  };
                }

                specifications (1) {
                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta1")
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                ])
                .unwrap()
                .with_variables(vec![
                    Variable::new("var1"),
                    Variable::new("var2"),
                    Variable::new("var3"),
                ])
                .unwrap()
                .with_locations(vec![
                    Location::new("loc1"),
                    Location::new("loc2"),
                    Location::new("loc3"),
                ])
                .unwrap()
                .initialize()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("loc1"), Location::new("loc2")).build(),
                    RuleBuilder::new(1, Location::new("loc2"), Location::new("loc3"))
                        .with_guard(BooleanExpression::BinaryExpression(
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Const(1)),
                            )),
                            BooleanConnective::And,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            )),
                        ))
                        .with_action(Action::new_reset(Variable::new("var3")))
                        .with_action(
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::Atom(Variable::new("var1"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                ])
                .unwrap()
                .with_initial_location_constraint(LocationConstraint::BinaryExpression(
                    Box::new(LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            IntegerOp::Sub,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    )),
                    BooleanConnective::Or,
                    Box::new(LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    )),
                ))
                .unwrap()
                .with_initial_variable_constraints(vec![
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var3"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Const(3)),
                        IntegerOp::Mul,
                        Box::new(IntegerExpression::Param(Parameter::new("f"))),
                    )),
                ))
                .unwrap()
                .build();

            let parser = ByMCParser;
            let got_ta = parser.parse_ta(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta)
        }

        #[test]
        fn test_parse_ta_2() {
            let test_spec = "
            skel test_ta {
                local loc;
                shared sha;
                parameters n;

                assumptions (1) {
                    n >= 1;
                }

                locations (3) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }/*loc*/
                inits (3) {
                    q0 == n;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                }/*in */
                rules (1) {
                    0: q0 -> q1
                    when (true)
                    do { sha' == sha + 1 };
                }

                specifications (0) {

                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
                .with_variables(vec![Variable::new("sha")])
                .unwrap()
                .with_parameters(vec![Parameter::new("n")])
                .unwrap()
                .with_locations(vec![
                    Location::new("q0"),
                    Location::new("q1"),
                    Location::new("q2"),
                ])
                .unwrap()
                .initialize()
                .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(1)),
                ))
                .unwrap()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q0"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_initial_variable_constraint(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("sha"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ))
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("q0"), Location::new("q1"))
                        .with_guard(BooleanExpression::True)
                        .with_action(
                            Action::new(
                                Variable::new("sha"),
                                IntegerExpression::Atom(Variable::new("sha"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                ])
                .unwrap()
                .build();

            let parser = ByMCParser;
            let got_ta = parser.parse_ta(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta)
        }

        #[test]
        fn test_parse_ta_2_invalid_component_numbers() {
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
                }

                specifications (5) {

                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
                .with_variables(vec![Variable::new("sha")])
                .unwrap()
                .with_parameters(vec![Parameter::new("n")])
                .unwrap()
                .with_locations(vec![
                    Location::new("q0"),
                    Location::new("q1"),
                    Location::new("q2"),
                ])
                .unwrap()
                .initialize()
                .with_resilience_condition(ParameterConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ComparisonOp::Geq,
                    Box::new(IntegerExpression::Const(1)),
                ))
                .unwrap()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q0"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_initial_variable_constraint(BooleanVarConstraint::ComparisonExpression(
                    Box::new(IntegerExpression::Atom(Variable::new("sha"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ))
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("q0"), Location::new("q1"))
                        .with_guard(BooleanExpression::True)
                        .with_action(
                            Action::new(
                                Variable::new("sha"),
                                IntegerExpression::Atom(Variable::new("sha"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                ])
                .unwrap()
                .build();

            let parser = ByMCParser::new();
            let got_ta = parser.parse_ta(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta)
        }

        #[test]
        fn test_parse_ta_3() {
            let test_spec = "
            skel test_ta {
                shared sha, var1, var2, var3;
                parameters n, t, f, p;

                assumptions (1) {
                    n >= 1;
                    n > 3 * f;
                    n < 3 * t;
                    p + n <= t / f;
                }

                locations (3) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }

                // my comment
                inits (3) {
                    q0 == n + f;
                    q1 == 0;
                    q2 == 0;
                    sha == 0;
                    var1 < 1;
                    var2 <= 0;
                }

                rules (1) {
                    0: q0 -> q1
                        when (true)
                        do { sha' == sha + 1 };
                    1: q0 -> q1
                        when (false)
                        do { unchanged(var1, var2, var3) };
                    2: q1 -> q2
                        when (var1 == 1 && var2 <= 0)
                        do { reset(var3); var1' == var1 + 1 };
                    3: q2 -> q1
                        when ( !(var1 < 1) || var3 <= n)
                        do { var3' == 0 };
                }

                specifications (0) {

                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
                .with_variables(vec![
                    Variable::new("sha"),
                    Variable::new("var1"),
                    Variable::new("var2"),
                    Variable::new("var3"),
                ])
                .unwrap()
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                    Parameter::new("p"),
                ])
                .unwrap()
                .with_locations(vec![
                    Location::new("q0"),
                    Location::new("q1"),
                    Location::new("q2"),
                ])
                .unwrap()
                .initialize()
                .with_resilience_conditions(vec![
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Const(3)),
                            IntegerOp::Mul,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Const(3)),
                            IntegerOp::Mul,
                            Box::new(IntegerExpression::Param(Parameter::new("t"))),
                        )),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("p"))),
                            IntegerOp::Add,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        )),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("t"))),
                            IntegerOp::Div,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    ),
                ])
                .unwrap()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q0"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            IntegerOp::Add,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_initial_variable_constraints(vec![
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("sha"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("q0"), Location::new("q1"))
                        .with_guard(BooleanExpression::True)
                        .with_action(
                            Action::new(
                                Variable::new("sha"),
                                IntegerExpression::Atom(Variable::new("sha"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(1, Location::new("q0"), Location::new("q1"))
                        .with_guard(BooleanExpression::False)
                        .build(),
                    RuleBuilder::new(2, Location::new("q1"), Location::new("q2"))
                        .with_guard(BooleanExpression::BinaryExpression(
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Const(1)),
                            )),
                            BooleanConnective::And,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                                ComparisonOp::Leq,
                                Box::new(IntegerExpression::Const(0)),
                            )),
                        ))
                        .with_actions(vec![
                            Action::new_reset(Variable::new("var3")),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::Atom(Variable::new("var1"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        ])
                        .build(),
                    RuleBuilder::new(3, Location::new("q2"), Location::new("q1"))
                        .with_guard(BooleanExpression::BinaryExpression(
                            Box::new(BooleanExpression::Not(Box::new(
                                BooleanVarConstraint::ComparisonExpression(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    ComparisonOp::Lt,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            ))),
                            BooleanConnective::Or,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var3"))),
                                ComparisonOp::Leq,
                                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            )),
                        ))
                        .with_actions(vec![Action::new_reset(Variable::new("var3"))])
                        .build(),
                ])
                .unwrap()
                .build();

            let parser = ByMCParser;
            let got_ta = parser.parse_ta(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta)
        }

        #[test]
        fn test_parse_ta_3_with_define() {
            let test_spec = "
            skel test_ta {
                shared sha, var1, var2, var3;
                parameters n, t, f, p;

                define THRESH_0 == 3 * f;
                define THRESH_1 == n + f;
                define THRESH_2 == 0;
                define THRESH_4 == n;

                assumptions (1) {
                    n >= 1;
                    n > THRESH_0;
                    n < 3 * t;
                    p + n <= t / f;
                }

                locations (3) {
                    q0: [0];
                    q1: [1];
                    q2: [2];
                }

                // my comment
                inits (3) {
                    q0 == THRESH_1;
                    q1 == THRESH_2;
                    q2 == THRESH_2;
                    sha == THRESH_2;
                    var1 < 1;
                    var2 <= THRESH_2;
                }

                rules (1) {
                    0: q0 -> q1
                        when (true)
                        do { sha' == sha + 1 };
                    1: q0 -> q1
                        when (false)
                        do { unchanged(var1, var2, var3) };
                    2: q1 -> q2
                        when (var1 == 1 && var2 <= THRESH_2)
                        do { reset(var3); var1' == var1 + 1 };
                    3: q2 -> q1
                        when ( !(var1 < 1) || var3 <= THRESH_4)
                        do { var3' == 0 };
                }

                specifications (0) {

                }
            }
            ";

            let expected_ta = GeneralThresholdAutomatonBuilder::new("test_ta")
                .with_variables(vec![
                    Variable::new("sha"),
                    Variable::new("var1"),
                    Variable::new("var2"),
                    Variable::new("var3"),
                ])
                .unwrap()
                .with_parameters(vec![
                    Parameter::new("n"),
                    Parameter::new("t"),
                    Parameter::new("f"),
                    Parameter::new("p"),
                ])
                .unwrap()
                .with_locations(vec![
                    Location::new("q0"),
                    Location::new("q1"),
                    Location::new("q2"),
                ])
                .unwrap()
                .initialize()
                .with_resilience_conditions(vec![
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ComparisonOp::Geq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Const(3)),
                            IntegerOp::Mul,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Const(3)),
                            IntegerOp::Mul,
                            Box::new(IntegerExpression::Param(Parameter::new("t"))),
                        )),
                    ),
                    ParameterConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("p"))),
                            IntegerOp::Add,
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                        )),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("t"))),
                            IntegerOp::Div,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    ),
                ])
                .unwrap()
                .with_initial_location_constraints(vec![
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q0"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::BinaryExpr(
                            Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            IntegerOp::Add,
                            Box::new(IntegerExpression::Param(Parameter::new("f"))),
                        )),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    LocationConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Location::new("q2"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_initial_variable_constraints(vec![
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("sha"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        ComparisonOp::Lt,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                    BooleanVarConstraint::ComparisonExpression(
                        Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                        ComparisonOp::Leq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ])
                .unwrap()
                .with_rules(vec![
                    RuleBuilder::new(0, Location::new("q0"), Location::new("q1"))
                        .with_guard(BooleanExpression::True)
                        .with_action(
                            Action::new(
                                Variable::new("sha"),
                                IntegerExpression::Atom(Variable::new("sha"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        )
                        .build(),
                    RuleBuilder::new(1, Location::new("q0"), Location::new("q1"))
                        .with_guard(BooleanExpression::False)
                        .build(),
                    RuleBuilder::new(2, Location::new("q1"), Location::new("q2"))
                        .with_guard(BooleanExpression::BinaryExpression(
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                ComparisonOp::Eq,
                                Box::new(IntegerExpression::Const(1)),
                            )),
                            BooleanConnective::And,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var2"))),
                                ComparisonOp::Leq,
                                Box::new(IntegerExpression::Const(0)),
                            )),
                        ))
                        .with_actions(vec![
                            Action::new_reset(Variable::new("var3")),
                            Action::new(
                                Variable::new("var1"),
                                IntegerExpression::Atom(Variable::new("var1"))
                                    + IntegerExpression::Const(1),
                            )
                            .unwrap(),
                        ])
                        .build(),
                    RuleBuilder::new(3, Location::new("q2"), Location::new("q1"))
                        .with_guard(BooleanExpression::BinaryExpression(
                            Box::new(BooleanExpression::Not(Box::new(
                                BooleanVarConstraint::ComparisonExpression(
                                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                                    ComparisonOp::Lt,
                                    Box::new(IntegerExpression::Const(1)),
                                ),
                            ))),
                            BooleanConnective::Or,
                            Box::new(BooleanVarConstraint::ComparisonExpression(
                                Box::new(IntegerExpression::Atom(Variable::new("var3"))),
                                ComparisonOp::Leq,
                                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                            )),
                        ))
                        .with_actions(vec![Action::new_reset(Variable::new("var3"))])
                        .build(),
                ])
                .unwrap()
                .build();

            let parser = ByMCParser;
            let got_ta = parser.parse_ta(test_spec).unwrap();

            assert_eq!(got_ta, expected_ta)
        }
    }
}

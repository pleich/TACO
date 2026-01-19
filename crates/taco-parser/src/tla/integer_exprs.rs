//! Module declaring helper functions to parse expressions over integers,
//! including boolean expressions over integers
//!
//! This module implements the parsing of expressions involving integers, such
//! as for example boolean expressions over integers or update expressions over
//! integers.

use std::any::TypeId;

use anyhow::Context;
use pest::{
    iterators::Pair,
    pratt_parser::{Assoc, PrattParser},
};
use taco_model_checker::eltl::ELTLExpression;
use taco_threshold_automaton::{
    expressions::{
        Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp,
        IsDeclared, Location, Parameter, Variable,
    },
    general_threshold_automaton::Action,
};

use crate::tla::{
    N_CORR_PROC, PROC_SET, Rule, TLAParsingContext, new_parsing_error, parse_identifier_to_t,
    try_parse_map_entry_constr_loc,
};

// Pratt parser responsible for maintaining operator precedence
//
// Here we simply borrow them from C++
// [see](https://en.cppreference.com/w/cpp/language/operator_precedence)
//
// Additionally, we define the precedence of the temporal operators
// - `G` (Globally) and `F` (Eventually) have the highest precedence
// - `!` (Not) has the second highest precedence
lazy_static::lazy_static! {
   pub(crate) static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Op};

        // Precedence is defined lowest to highest
        PrattParser::new()
            .op(Op::infix(Rule::or, Assoc::Left))
            .op(Op::infix(Rule::implication, Assoc::Right))
            .op(Op::infix(Rule::and, Assoc::Left))
            .op(Op::infix(Rule::equal, Assoc::Left) | Op::infix(Rule::not_equal, Assoc::Left))
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

/// Parse a single ltl specification
///
/// This function parses a single ltl specification and returns the name of the
/// specification and the ltl expression.
pub(crate) fn parse_ltl_specification<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &TLAParsingContext<'_>,
) -> Result<(String, ELTLExpression), anyhow::Error>
where
    T: IsDeclared<Variable> + IsDeclared<Location> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::ltl_spec_declaration,
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
/// The function returns an error if the expression refers to an unknown location
pub(crate) fn parse_ltl_expr<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &TLAParsingContext<'_>,
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
    ctx: &TLAParsingContext<'_>,
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
                new_parsing_error("Failed to parse inner ltl expression. This is most likely due to an unknown identifier", span)
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

/// Parse boolean_atom
#[inline(always)]
fn parse_boolean_atom<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &TLAParsingContext,
) -> Result<BooleanExpression<T>, anyhow::Error>
where
    T: Atomic + 'static,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::int_bool_atom,
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
        Rule::int_bool_expr => parse_int_boolean_expr(pair, builder, ctx),
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

/// Parse integer constant
///
/// Parses a pair of type `integer_const` into a `u32`
#[inline(always)]
pub(crate) fn parse_integer_const(pair: Pair<'_, Rule>) -> u32 {
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
/// Parses a constraint of the form
///     `Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})`
/// into an `IntegerExpression::Atom(Location::new("loc0"))`
///
/// This function panics if you attempt to parse it into a type other then
/// `IntegerExpression<Location`
fn parse_cardinality_expr<T>(pair: Pair<'_, Rule>) -> Result<IntegerExpression<T>, anyhow::Error>
where
    T: Atomic + 'static,
{
    debug_assert!(
        pair.as_rule() == Rule::cardinality_expr,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    // Cardinality constraints are a special case.
    // We only support parsing them into a location
    if TypeId::of::<T>() != TypeId::of::<Location>() {
        let parse_err = new_parsing_error(
            "Cardinality constraint can only be parsed into a constraint over locations.",
            pair.as_span(),
        );
        return Err(parse_err).with_context(|| "Error while parsing cardinality");
    }

    let mut inner_pairs = pair.into_inner();

    let elem_pair = inner_pairs.next().expect("Missing: Process identifier");
    let elem_ident: String = parse_identifier_to_t(&elem_pair);

    let set_ident_pair = inner_pairs.next().expect("Missing: Process set identifier");
    let set_ident: String = parse_identifier_to_t(&set_ident_pair);
    if set_ident != PROC_SET {
        let parse_err = new_parsing_error(
            format!("Cardinality constraint should be over the set of processes '{PROC_SET}'"),
            set_ident_pair.as_span(),
        );
        return Err(parse_err).with_context(|| "Error while parsing cardinality constraint: ");
    }

    let set_locs: Vec<T> = inner_pairs
        .map(|p| try_parse_map_entry_constr_loc(p, &elem_ident))
        .collect::<Result<Vec<_>, _>>()
        .with_context(|| "Error while parsing cardinality constraint: ")?;

    debug_assert!(!set_locs.is_empty());

    let mut it_set_locs = set_locs.into_iter();
    let first = IntegerExpression::Atom(it_set_locs.next().unwrap());
    let res = it_set_locs.fold(first, |acc, x| {
        IntegerExpression::BinaryExpr(
            Box::new(acc),
            IntegerOp::Add,
            Box::new(IntegerExpression::Atom(x)),
        )
    });

    Ok(res)
}

/// Parse integer atom
///
/// Returns an integer expression if the pair is a constant, known identifier,
/// cardinality expression or could be parsed to an expression.
///
/// Returns an error if the identifier was not declared with the identifier name
fn parse_integer_atom<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &TLAParsingContext,
) -> Result<IntegerExpression<T>, anyhow::Error>
where
    T: Atomic + 'static,
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
            // Check whether an integer macro has been declared
            let name: String = parse_identifier_to_t(&pair);
            if ctx.int_macro.contains_key(&name) {
                return parse_integer_expr(ctx.int_macro[&name].clone(), builder, ctx);
            }

            // Try to parse it into the atom and check whether it is declared
            let atom = parse_identifier_to_t(&pair);
            if builder.is_declared(&atom) {
                return Ok(IntegerExpression::Atom(atom));
            }

            // Try to parse it into the atom and check whether it is declared
            let param = parse_identifier_to_t(&pair);
            if builder.is_declared(&param) || pair.as_str() == N_CORR_PROC {
                return Ok(IntegerExpression::Param(param));
            }

            let parse_err = new_parsing_error(
                format!("Unknown identifier: '{}'", pair.as_str()),
                pair.as_span(),
            );

            Err(parse_err).with_context(|| "Failed to parse integer expression: ")
        }
        Rule::integer_expr => parse_integer_expr(pair, builder, ctx),
        Rule::cardinality_expr => parse_cardinality_expr(pair),
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
    ctx: &TLAParsingContext,
) -> Result<IntegerExpression<T>, anyhow::Error>
where
    T: Atomic + 'static,
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
        Rule::not_equal => ComparisonOp::Neq,
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

/// Parse a pair of type `comparison_expr` into a [CompExpr]
pub fn parse_comparison_expr<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &TLAParsingContext,
) -> Result<CompExpr<T>, anyhow::Error>
where
    T: Atomic + 'static,
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

/// Parse an expression of type `int_bool_expr` into a `BooleanExpression`
pub(crate) fn parse_int_boolean_expr<T, U>(
    pair: Pair<'_, Rule>,
    builder: &U,
    ctx: &TLAParsingContext,
) -> Result<BooleanExpression<T>, anyhow::Error>
where
    T: Atomic + 'static,
    U: IsDeclared<T> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::int_bool_expr,
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

/// Parse an assignment expression of an action into the corresponding list of
/// actions
fn parse_assignment_expression<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &TLAParsingContext,
) -> Result<Vec<Action>, Box<pest::error::Error<()>>>
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

    let act = Action::new(var, expr);

    if let Err(err) = act {
        return Err(new_parsing_error(
            format!("Failed to parse effect of action: {err}"),
            span,
        ));
    }

    Ok(vec![act.unwrap()])
}

/// Parse a pair of type `integer_update` into an [Action]
pub(crate) fn parse_integer_update_expr<T>(
    pair: Pair<'_, Rule>,
    builder: &T,
    ctx: &TLAParsingContext,
) -> Result<Vec<Action>, Box<pest::error::Error<()>>>
where
    T: IsDeclared<Variable> + IsDeclared<Parameter>,
{
    debug_assert!(
        pair.as_rule() == Rule::integer_update,
        "Got rule {:?} for {}",
        pair.as_rule(),
        pair.as_str()
    );

    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::unchanged_expr => Ok(vec![]),
        Rule::assignment_expr => parse_assignment_expression(pair, builder, ctx),
        _ => unreachable!(
            "Unknown rule for action expression {:?}: {}",
            pair.as_rule(),
            pair.as_str()
        ),
    }
}

#[cfg(test)]
mod tests {

    use pest::Parser;
    use taco_model_checker::eltl::ELTLExpression;
    use taco_threshold_automaton::{
        expressions::{
            BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp,
            Location, Parameter, Variable,
        },
        general_threshold_automaton::{Action, builder::GeneralThresholdAutomatonBuilder},
    };

    use crate::tla::{
        PestTLAParser, Rule, TLAParsingContext,
        integer_exprs::{
            parse_cardinality_expr, parse_int_boolean_expr, parse_integer_const,
            parse_integer_update_expr, parse_ltl_specification,
        },
    };

    #[test]
    fn test_parse_integer_const() {
        let input = "42";

        let mut pairs = PestTLAParser::parse(Rule::integer_const, input).unwrap();
        let pair = pairs.next().unwrap();

        let loc = parse_integer_const(pair);

        assert_eq!(loc, 42);
    }

    #[test]
    fn test_parse_int_bool() {
        let input = "var1 = 42";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let loc = parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(
            loc,
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(42))
            )
        );
    }

    #[test]
    fn test_parse_int_bool_div() {
        let input = "var1 <= 42 / -2";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let loc = parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(
            loc,
            BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                ComparisonOp::Leq,
                Box::new(IntegerExpression::BinaryExpr(
                    Box::new(IntegerExpression::Const(42)),
                    IntegerOp::Div,
                    Box::new(IntegerExpression::Neg(Box::new(IntegerExpression::Const(
                        2
                    ))))
                ))
            )
        );
    }

    #[test]
    fn test_parse_int_bool_const() {
        let input = "TRUE";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test").initialize();

        let ctx = TLAParsingContext::new();

        let loc: BooleanExpression<Variable> =
            parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(loc, BooleanExpression::True);

        let input = "FALSE";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test").initialize();

        let ctx = TLAParsingContext::new();

        let loc: BooleanExpression<Variable> =
            parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(loc, BooleanExpression::False);
    }

    #[test]
    fn test_parse_int_bool_disj_conj() {
        let input = "TRUE \\/ FALSE";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test").initialize();

        let ctx = TLAParsingContext::new();

        let loc: BooleanExpression<Variable> =
            parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(
            loc,
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::Or,
                Box::new(BooleanExpression::False)
            )
        );

        let input = "TRUE /\\ FALSE";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test").initialize();

        let ctx = TLAParsingContext::new();

        let loc: BooleanExpression<Variable> =
            parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(
            loc,
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::And,
                Box::new(BooleanExpression::False)
            )
        );

        let input = "~(TRUE /\\ FALSE)";

        let mut pairs = PestTLAParser::parse(Rule::int_bool_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test").initialize();

        let ctx = TLAParsingContext::new();

        let loc: BooleanExpression<Variable> =
            parse_int_boolean_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(
            loc,
            BooleanExpression::Not(Box::new(BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::And,
                Box::new(BooleanExpression::False)
            )))
        );
    }

    #[test]
    fn test_parse_int_update() {
        let input = "var1' = var1 + (42 + 0)";

        let mut pairs = PestTLAParser::parse(Rule::integer_update, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let loc = parse_integer_update_expr(pair, &builder, &ctx).unwrap();

        assert_eq!(
            loc,
            vec![
                Action::new(
                    Variable::new("var1"),
                    IntegerExpression::BinaryExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                        IntegerOp::Add,
                        Box::new(IntegerExpression::Const(42)),
                    )
                )
                .unwrap()
            ]
        );
    }

    #[test]
    fn test_parse_int_update_err() {
        let input = "var1' = unknown";

        let mut pairs = PestTLAParser::parse(Rule::integer_update, input).unwrap();
        let pair = pairs.next().unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let loc = parse_integer_update_expr(pair, &builder, &ctx);
        assert!(loc.is_err(), "Got: {:?}", loc.unwrap());
    }

    #[test]
    fn test_parse_cardinality() {
        let input = "Cardinality({p \\in Processes : ProcessesLocations[p] = \"loc0\"})";

        let mut pairs = PestTLAParser::parse(Rule::cardinality_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let loc = parse_cardinality_expr(pair).unwrap();

        assert_eq!(loc, IntegerExpression::Atom(Location::new("loc0")));
    }

    #[test]
    fn test_parse_cardinality_err_on_unkown_proc() {
        let input = "Cardinality({p \\in Something : ProcessesLocations[p] = \"loc0\"})";

        let mut pairs = PestTLAParser::parse(Rule::cardinality_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let loc: Result<IntegerExpression<Location>, anyhow::Error> = parse_cardinality_expr(pair);
        assert!(loc.is_err())
    }

    #[test]
    fn test_parse_cardinality_disj() {
        let input = "Cardinality({p \\in Processes : ProcessesLocations[p] = \"loc0\" \\/ ProcessesLocations[p] = \"loc1\"})";

        let mut pairs = PestTLAParser::parse(Rule::cardinality_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let loc = parse_cardinality_expr(pair).unwrap();

        assert_eq!(
            loc,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                IntegerOp::Add,
                Box::new(IntegerExpression::Atom(Location::new("loc1")))
            )
        );
    }

    #[test]
    #[should_panic]
    fn test_parse_card_param_panics() {
        let input = "Cardinality({p \\in Processes : ProcessesLocations[p] = \"loc0\"})";

        let mut pairs = PestTLAParser::parse(Rule::cardinality_expr, input).unwrap();
        let pair = pairs.next().unwrap();

        let loc = parse_cardinality_expr(pair).unwrap();

        assert_eq!(loc, IntegerExpression::Atom(Parameter::new("loc0")));
    }

    #[test]
    fn test_ltl_spec_parses() {
        let input = "unforg == 
        var1 = 0 => ([] (loc0 = 0) \\/ ~(<>( Cardinality({p \\in Processes : ProcessesLocations[p] = \"loc0\"}) > 1)))
        ";

        let mut pairs = PestTLAParser::parse(Rule::ltl_spec_declaration, input).unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .with_location(Location::new("loc0"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let got_ltl_spec = parse_ltl_specification(pairs.next().unwrap(), &builder, &ctx).unwrap();

        let expected_ltl_spec = (
            "unforg".to_string(),
            ELTLExpression::Implies(
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("var1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Or(
                    Box::new(ELTLExpression::Globally(Box::new(
                        ELTLExpression::LocationExpr(
                            Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                            ComparisonOp::Eq,
                            Box::new(IntegerExpression::Const(0)),
                        ),
                    ))),
                    Box::new(ELTLExpression::Not(Box::new(ELTLExpression::Eventually(
                        Box::new(ELTLExpression::LocationExpr(
                            Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                            ComparisonOp::Gt,
                            Box::new(IntegerExpression::Const(1)),
                        )),
                    )))),
                )),
            ),
        );

        assert_eq!(got_ltl_spec, expected_ltl_spec)
    }

    #[test]
    fn test_ltl_spec_parses_bool_const() {
        let input = "unforg == TRUE
        ";

        let mut pairs = PestTLAParser::parse(Rule::ltl_spec_declaration, input).unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .with_location(Location::new("loc0"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let got_ltl_spec = parse_ltl_specification(pairs.next().unwrap(), &builder, &ctx).unwrap();

        let expected_ltl_spec = ("unforg".to_string(), ELTLExpression::True);

        assert_eq!(got_ltl_spec, expected_ltl_spec);

        let input = "unforg == FALSE
        ";

        let mut pairs = PestTLAParser::parse(Rule::ltl_spec_declaration, input).unwrap();

        let builder = GeneralThresholdAutomatonBuilder::new("test")
            .with_variable(Variable::new("var1"))
            .unwrap()
            .with_location(Location::new("loc0"))
            .unwrap()
            .initialize();

        let ctx = TLAParsingContext::new();

        let got_ltl_spec = parse_ltl_specification(pairs.next().unwrap(), &builder, &ctx).unwrap();

        let expected_ltl_spec = ("unforg".to_string(), ELTLExpression::False);

        assert_eq!(got_ltl_spec, expected_ltl_spec)
    }
}

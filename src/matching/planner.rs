//! Given a Constraint, how should we figure out the corresponding
//! matches?
//!
//! There is no universally optimal answer to this question,
//! especially once we go past binary joins.  Start with a criminally
//! bad plan that's easy to express in Differential Dataflow.
use super::plan::Source;
use super::Constraint;
use super::Plan;
use super::PredicateFormula;
use crate::unification::MetaVar;
use std::collections::HashMap;

/// Returns a Plan to match `constraint`, yielding capture tuples
/// that match the shape `constraint.captures()`.
///
/// # Errors
///
/// Returns `Err` when the `sources`' shapes does not match the
/// `PredicateFormula`e in `constraint`.
pub fn plan_constraint<H: std::hash::BuildHasher>(
    constraint: &Constraint,
    sources: &HashMap<String, Source, H>,
) -> Result<Plan, &'static str> {
    let mut accumulator: Option<Plan> = None;

    // A good planner would try to be smart about the order in which
    // we perform binary joins (or go past binary joins)... Let's do
    // the bare minimum with natural joins all the way.
    for conjunct in constraint.conjuncts().iter() {
        let formula_plan = plan_formula(conjunct, sources)?;

        accumulator = match accumulator {
            None => Some(formula_plan),
            Some(acc) => Some(Plan::natural_join(vec![acc, formula_plan])?),
        }
    }

    // Natural joins may yield useless values.  Drop everything but
    // what we need for the captures.
    let captures: Vec<MetaVar> = constraint.captures().iter().cloned().collect();

    match accumulator {
        None => {
            // If there's nothing to join on, there must not be any
            // capture.  Since there's no match condition, we always
            // successfully find the empty tuple.
            assert!(captures.is_empty());
            Plan::constant()
        }
        Some(acc) => Plan::project(acc, &captures),
    }
}

/// Returns a plan to match `formula` against its source, yielding the
/// formula's captures.
fn plan_formula<H: std::hash::BuildHasher>(
    formula: &PredicateFormula,
    sources: &HashMap<String, Source, H>,
) -> Result<Plan, &'static str> {
    let source = sources
        .get(&formula.predicate)
        .ok_or("Predicate not found")?
        .clone();
    Plan::filter(source, &formula.pattern)
}

#[test]
fn plan_constraint_smoke_test() {
    use super::Constraint;
    use super::PredicateFormula;
    use crate::unification::Element;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p = PredicateFormula::new(
        "p",
        [Element::Reference(x.clone()), Element::Reference(y.clone())]
            .iter()
            .cloned(),
    );
    let q = PredicateFormula::new(
        "q",
        [Element::Reference(y.clone()), Element::Reference(z.clone())]
            .iter()
            .cloned(),
    );

    let constraint =
        Constraint::new([y.clone()].iter().cloned().collect(), vec![p, q]).expect("ok");
    let mut sources = HashMap::new();
    sources.insert("p".into(), Source::new("p", 2));
    sources.insert("q".into(), Source::new("q", 2));
    let plan = plan_constraint(&constraint, &sources).expect("ok");

    assert_eq!(plan.result(), &[y.clone()]);
}

#[test]
fn plan_constraint_empty() {
    use super::Constraint;
    use std::collections::BTreeSet;

    let constraint = Constraint::new(BTreeSet::new(), Vec::new()).expect("ok");
    let sources = HashMap::new();
    let plan = plan_constraint(&constraint, &sources).expect("ok");

    assert_eq!(plan.result(), &[]);
}

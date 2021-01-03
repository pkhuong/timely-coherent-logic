//! Given a Constraint or a sequent's antecendent Constraint and list of
//! consequent Constraints, how should we figure out the corresponding
//! matches?
//!
//! There is no universally optimal answer to this question,
//! especially once we go past binary joins.  Start with a criminally
//! bad plan that's easy to express in Differential Dataflow.
//!
//! Planning for a full sequent isn't difficult, but might be
//! surprising.  A coherent logic sequent matches a conjunction of
//! antecedents on the left-hand (top) side, from which we can infer
//! any one of a set of consequents on the right-hand (bottom) side.
//! The key is that we can avoid instantiating a sequent when one of
//! its consequents already holds.
//!
//! The `plan_sequent` function constructs a query plan that returns
//! all captures matching the left-hand side of a sequent, and none of
//! its right-hand sides.
//!
//! We expect each of the consequents' "captures" to only include a
//! non-strict subset of the antecedents'.  Any other metavariable
//! "matched" in a consequent is an existential; they are replaced
//! with fresh variables when instantiating a consequent.  When
//! matching, they are treated as non-capture $$\forall$$: a
//! consequent of the form $$\exists y: p(x, y)$$ is already satisfied
//! whenever there already exists such a $$y,$$ so we want to avoid
//! all $$x$$ such that $$p(x, y)$$ is true, for all $y$.
use super::plan::Source;
use super::Constraint;
use super::Plan;
use super::PredicateFormula;
use crate::unification::MetaVar;
use std::collections::HashMap;

/// Returns a plan to match `constraint`, yielding capture tuples that
/// match `constraint.captures()`, except for those that would
/// corresponding to one of the consequents.  The consequents'
/// captures must be a subset of `constraint.captures()`; this is
/// typically achieved by constructing the consequents with
/// [`Constraint::new_partial`](super::Constraint::new_partial).
///
/// # Errors
///
/// Returns `Err` if any of the `consequents`'s captured `MetaVar`s
/// aren't found in the `antecedents`', or on shape mismatch between
/// the `sources` and the `PredicateFormula`e in the antecedents or
/// consequents.
pub fn plan_sequent<'a, I, H>(
    antecedents: &Constraint,
    consequents: I,
    sources: &HashMap<String, Source, H>,
) -> Result<Plan, &'static str>
where
    I: IntoIterator<Item = &'a Constraint>,
    H: std::hash::BuildHasher,
{
    let mut match_plan = plan_constraint(antecedents, sources)?;

    for consequent in consequents {
        if !consequent.captures().is_subset(antecedents.captures()) {
            return Err("Consequent's capture not included in antecedents'.");
        }

        let non_match_plan = plan_constraint(consequent, sources)?;
        match_plan = Plan::antijoin(
            match_plan,
            &consequent.captures().iter().cloned().collect::<Vec<_>>(),
            vec![non_match_plan],
        )?;
    }

    Ok(match_plan)
}

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

#[test]
fn test_plan_sequent_smoke_test() {
    use super::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;

    // Plan a dummy axiom, $$p(x, y) -> \exists z: q(x, z)$$
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p = PredicateFormula::new(
        "p",
        vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
    );

    let q = PredicateFormula::new(
        "q",
        vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
    );

    let antecedent = Constraint::new([x.clone()].iter().cloned().collect(), vec![p]).expect("ok");
    let consequent = Constraint::new_partial(antecedent.captures().clone(), vec![q]);

    let mut sources = HashMap::new();
    sources.insert("p".into(), Source::new("p", 2));
    sources.insert("q".into(), Source::new("q", 2));

    let plan = plan_sequent(&antecedent, &[consequent], &sources).expect("ok");

    assert_eq!(plan.result(), &[x.clone()]);
}

#[test]
fn test_plan_sequent_bad_consequent() {
    use super::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;

    // Plan a dummy axiom, $$p(x, y) -> \exists z: q(x, z),$$
    // but set the capture incorrectly for the consequent.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p = PredicateFormula::new(
        "p",
        vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
    );

    let q = PredicateFormula::new(
        "q",
        vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
    );

    let antecedent = Constraint::new([x.clone()].iter().cloned().collect(), vec![p]).expect("ok");
    let consequent =
        Constraint::new([x.clone(), z.clone()].iter().cloned().collect(), vec![q]).expect("ok");

    let mut sources = HashMap::new();
    sources.insert("p".into(), Source::new("p", 2));
    sources.insert("q".into(), Source::new("q", 2));

    assert!(plan_sequent(&antecedent, &[consequent], &sources).is_err());
}

//! Matching expressions describe what we would like to match on, and
//! what metavariables we wish to capture in order to instantiate
//! right-hand sides.
use crate::unification::{Element, MetaVar};
use std::collections::BTreeSet;

/// A predicate formula represents an expression of the form
/// `predicate(pattern*)` (which must be true).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PredicateFormula {
    pub predicate: String,
    pub pattern: Vec<Element>,
}

impl PredicateFormula {
    #[must_use]
    pub fn new<I: IntoIterator<Item = Element>>(predicate: &str, pattern: I) -> Self {
        Self {
            predicate: predicate.into(),
            pattern: pattern.into_iter().collect(),
        }
    }

    /// Inserts all `MetaVars` in the pattern into `dst`.
    #[must_use]
    pub fn insert_metavars(&self, mut dst: BTreeSet<MetaVar>) -> BTreeSet<MetaVar> {
        for elt in &self.pattern {
            if let Element::Reference(mv) = elt {
                dst.insert(mv.clone());
            }
        }

        dst
    }
}

/// A `Constraint` is a set of `MetaVar`s to capture, and a list of
/// `PredicateFormula`e that must all be true for the `Constraint` to
/// hold for a given capture.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Constraint {
    /// Set of metavars to report back.
    captures: BTreeSet<MetaVar>,
    /// Set of all metavars that appear in the conjuncts below.
    /// This is always a (non-strict) superset of `captures`.
    ///
    /// We use an ordered set because we expect its ordering to
    /// reflect the structure of the expressions in `conjuncts`.
    metavars: BTreeSet<MetaVar>,
    /// List of formulas that must all hold.  Logically, this is a
    /// set, but we want to avoid hashing for reproducibility and
    /// testability.
    conjuncts: BTreeSet<PredicateFormula>,
}

impl Constraint {
    /// Returns a new constraint to report all `captures` that match
    /// the `conjuncts`.
    ///
    /// This function constructs a `Constraint` for the left-hand side
    /// of an implication axiom.
    ///
    /// # Errors
    ///
    /// Returns `Err` if a `MetaVar` in `captures` is not matched in
    /// any of the `conjuncts`.
    pub fn new<I: IntoIterator<Item = PredicateFormula>>(
        captures: BTreeSet<MetaVar>,
        conjuncts: I,
    ) -> Result<Self, &'static str> {
        let conjunct_set = conjuncts.into_iter().collect();
        let metavars = extract_metavars(&conjunct_set);
        if !captures.is_subset(&metavars) {
            return Err("Captures must appear in conjuncts (must be rigid).");
        }

        Ok(Self {
            captures,
            metavars,
            conjuncts: conjunct_set,
        })
    }

    /// Returns a new constraint to report the subset of `captures`
    /// that appear in `conjuncts`, for all that match the
    /// `conjuncts`.
    ///
    /// This function constructs a `Constraint` for one of an
    /// implication axiom's right-hand sides.
    #[must_use]
    pub fn new_partial<I: IntoIterator<Item = PredicateFormula>>(
        mut captures: BTreeSet<MetaVar>,
        conjuncts: I,
    ) -> Self {
        let conjunct_set = conjuncts.into_iter().collect();
        let metavars = extract_metavars(&conjunct_set);
        captures = captures.intersection(&metavars).cloned().collect();

        Self {
            captures,
            metavars,
            conjuncts: conjunct_set,
        }
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn captures(&self) -> &BTreeSet<MetaVar> {
        &self.captures
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn metavars(&self) -> &BTreeSet<MetaVar> {
        &self.metavars
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn conjuncts(&self) -> &BTreeSet<PredicateFormula> {
        &self.conjuncts
    }
}

/// Returns the `MetaVar`s referenced in at least one of the `conjuncts`.
fn extract_metavars<'a, I>(conjuncts: I) -> BTreeSet<MetaVar>
where
    I: IntoIterator<Item = &'a PredicateFormula>,
{
    let mut ret = BTreeSet::<MetaVar>::new();

    for formula in conjuncts {
        ret = formula.insert_metavars(ret);
    }

    ret
}

#[test]
fn predicate_smoke_test() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let formula = PredicateFormula::new(
        "p",
        [
            Element::Reference(x.clone()),
            Element::Reference(y.clone()),
            Element::Reference(x.clone()),
        ]
        .iter()
        .cloned(),
    );

    // Get the correct variable set for an empty initial set.
    assert_eq!(
        formula.insert_metavars(BTreeSet::new()),
        [x.clone(), y.clone()].iter().cloned().collect()
    );

    // ... and with a pre-initialised set.
    assert_eq!(
        formula.insert_metavars([z.clone()].iter().cloned().collect()),
        [x.clone(), y.clone(), z.clone()].iter().cloned().collect()
    );
}

#[test]
fn constraint_happy_path() {
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

    let captures = [x.clone(), y.clone()].iter().cloned().collect();
    let constraint = Constraint::new(captures, [p, q].iter().cloned()).expect("ok");
    assert_eq!(
        *constraint.captures(),
        [x.clone(), y.clone()].iter().cloned().collect()
    );
    assert_eq!(
        *constraint.metavars(),
        [x.clone(), y.clone(), z.clone()].iter().cloned().collect()
    );
    assert_eq!(constraint.conjuncts().len(), 2);
}

#[test]
fn constraint_missing_capture() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p = PredicateFormula::new(
        "p",
        [Element::Reference(x.clone()), Element::Reference(y.clone())]
            .iter()
            .cloned(),
    );

    let captures = [x.clone(), y.clone(), z.clone()].iter().cloned().collect();
    assert!(Constraint::new(captures, [p].iter().cloned()).is_err());
}

#[test]
fn constraint_missing_capture_partial() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p = PredicateFormula::new(
        "p",
        [Element::Reference(x.clone()), Element::Reference(y.clone())]
            .iter()
            .cloned(),
    );

    let captures = [x.clone(), z.clone()].iter().cloned().collect();
    let constraint = Constraint::new_partial(captures, [p].iter().cloned());
    assert_eq!(
        *constraint.captures(),
        [x.clone()].iter().cloned().collect()
    );
    assert_eq!(
        *constraint.metavars(),
        [x.clone(), y.clone()].iter().cloned().collect()
    );
    assert_eq!(constraint.conjuncts().len(), 1);
}

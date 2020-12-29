//! Matching expressions describe what we would like to match on, and
//! what metavariables we wish to capture in order to instantiate
//! right-hand sides.
use crate::unification::{Element, MetaVar};
use std::collections::BTreeSet;

/// A predicate formula represents an expression of the form
/// `predicate(pattern*)` (which must be true).
#[derive(Clone, Debug)]
pub struct PredicateFormula {
    pub predicate: String,
    pub pattern: Vec<Element>,
}

impl PredicateFormula {
    pub fn new(predicate: &str, pattern: &[Element]) -> Self {
        Self {
            predicate: predicate.into(),
            pattern: pattern.into(),
        }
    }

    /// Inserts all `MetaVars` in the pattern into `dst`.
    pub fn insert_metavars(&self, mut dst: BTreeSet<MetaVar>) -> BTreeSet<MetaVar> {
        for elt in self.pattern.iter() {
            if let Element::Reference(mv) = elt {
                dst.insert(mv.clone());
            }
        }

        dst
    }
}

/// A `Constraint` is a set of metavars to capture, and a list of
/// `PredicateFormula`e that must all be true for the `Constraint` to
/// hold for a given capture.
#[derive(Clone, Debug)]
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
    conjuncts: Vec<PredicateFormula>,
}

impl Constraint {
    /// Returns a new constraint to report all `captures` that match
    /// the `conjuncts`.
    ///
    /// This function constructs a `Constraint` for the left-hand side
    /// of an implication axiom.
    pub fn new(
        captures: BTreeSet<MetaVar>,
        conjuncts: Vec<PredicateFormula>,
    ) -> Result<Self, &'static str> {
        let metavars = extract_metavars(&conjuncts);
        if !captures.is_subset(&metavars) {
            return Err("Captures must appear in conjuncts (must be rigid).");
        }

        Ok(Self {
            captures,
            metavars,
            conjuncts,
        })
    }

    /// Returns a new constraint to report the subset of `captures`
    /// that appear in `conjuncts`, for all that match the
    /// `conjuncts`.
    ///
    /// This function constructs a `Constraint` for one of an
    /// implication axiom's right-hand sides.
    pub fn new_partial(mut captures: BTreeSet<MetaVar>, conjuncts: Vec<PredicateFormula>) -> Self {
        let metavars = extract_metavars(&conjuncts);
        captures = captures.intersection(&metavars).cloned().collect();

        Self {
            captures,
            metavars,
            conjuncts,
        }
    }

    #[cfg(not(tarpaulin_include))]
    pub fn captures(&self) -> &BTreeSet<MetaVar> {
        &self.captures
    }

    #[cfg(not(tarpaulin_include))]
    pub fn metavars(&self) -> &BTreeSet<MetaVar> {
        &self.metavars
    }

    #[cfg(not(tarpaulin_include))]
    pub fn conjuncts(&self) -> &[PredicateFormula] {
        &self.conjuncts
    }
}

/// Returns the MetaVars referenced in at least one of the `conjuncts`.
fn extract_metavars(conjuncts: &[PredicateFormula]) -> BTreeSet<MetaVar> {
    let mut ret = BTreeSet::<MetaVar>::new();

    for formula in conjuncts.iter() {
        ret = formula.insert_metavars(ret);
    }

    ret
}

#[test]
fn predicate_smoke_test() {
    use crate::ground::Variable;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let formula = PredicateFormula::new(
        "p",
        &[
            Element::Reference(x.clone()),
            Element::Constant(Variable::new(1)),
            Element::Reference(y.clone()),
            Element::Reference(x.clone()),
        ],
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
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    );

    let q = PredicateFormula::new(
        "q",
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    );

    let captures = [x.clone(), y.clone()].iter().cloned().collect();
    let constraint = Constraint::new(captures, [p, q].into()).expect("ok");
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
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    );

    let captures = [x.clone(), y.clone(), z.clone()].iter().cloned().collect();
    assert!(Constraint::new(captures, [p].into()).is_err());
}

#[test]
fn constraint_missing_capture_partial() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p = PredicateFormula::new(
        "p",
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    );

    let captures = [x.clone(), z.clone()].iter().cloned().collect();
    let constraint = Constraint::new_partial(captures, [p].into());
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

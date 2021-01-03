//! Given a Constraint, how do we want to apply filters, joins, and
//! project away data that isn't needed now that joins are done?  The
//! data structures defined in this module describe a planning
//! function's answer to that question.
//!
//! For the foreseeable future, we will stick to nodes that can be
//! directly translated to differential dataflow operators.
use crate::unification::{Element, MetaVar, MultiProjection, Pattern, Projection};
use std::collections::{BTreeSet, HashMap, HashSet};

/// A source is a collection from which we can read tuples of
/// `Variable`s.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Source {
    pub predicate_name: String,
    pub arity: usize,
}

impl Source {
    #[must_use]
    pub fn new(predicate_name: &str, arity: usize) -> Self {
        Source {
            predicate_name: predicate_name.into(),
            arity,
        }
    }
}

/// A Plan represents (a tree of) steps to perform in order to find
/// captured variable values that match a given Constraint.  The
/// toplevel (root) operator for a Constraint should yield exactly the
/// metavariables in the `Constraint`'s capture set.
///
/// A Plan node always yields a tuples of `Variable`s matching its
/// `result` list of metavariables.
#[derive(Debug, Hash, Eq, PartialEq)]
pub struct Plan {
    /// Executing this plan yields tuple of `Variable`s with this
    /// shape.
    result: Vec<MetaVar>,
    op: PlanOp,
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub enum PlanOp {
    /// Unconditionally yields an empty tuple `()`.
    Constant,
    /// A Filter operator takes a source of facts, and yields captures
    /// for facts that match the `pattern`.
    Filter(FilterOp),
    /// A Project operator takes an operator's results, and restructures
    /// each capture tuple in that collection.
    Project(ProjectOp),
    /// A Join operator takes a sequence of operators, equijoins their
    /// facts by the `Variable`s matching `key`, and yields a new capture
    /// by extracting `result` from the combined fact tuple.
    Join(JoinOp),
    /// An Antijoin operator is defined by a list of metavars `key`;
    /// an operator accepts a first "minuend" operator and a list of
    /// "subtrahend" operators, and yields all items from the minuend
    /// that do not match anything in the minuends.
    ///
    /// The subtrahends' shapes must all match the `key`.
    Antijoin(AntijoinOp),
}

impl Plan {
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn result(&self) -> &[MetaVar] {
        &self.result
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn op(&self) -> &PlanOp {
        &self.op
    }

    /// Constructs a plan that always yields an empty capture.
    ///
    /// # Errors
    ///
    /// This function currently cannot fail.
    pub fn constant() -> Result<Self, &'static str> {
        Ok(Plan {
            result: Vec::new(),
            op: PlanOp::Constant,
        })
    }

    /// Constructs a plan that returns captures in `pattern`, for
    /// tuples of `source` that match the pattern.
    ///
    /// # Errors
    ///
    /// Returns `Err` when `pattern`'s shape does not match `source`'s.
    pub fn filter(source: Source, pattern: &[Element]) -> Result<Self, &'static str> {
        FilterOp::make(source, pattern)
    }

    /// Constructs a plan that restructures the `input`'s tuples to
    /// match `kept`.
    ///
    /// # Errors
    ///
    /// Returns `Err` when `kept` includes `MetaVar`s absent from
    /// `input`'s result shape.
    pub fn project(input: Plan, kept: &[MetaVar]) -> Result<Self, &'static str> {
        ProjectOp::make(input, kept)
    }

    /// Constructs a plan that joins the `inputs`'s tuples that have
    /// equal values for `key`, and extracts `kept` metavars from the
    /// result.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the join `key` is partially absent from any
    /// of the `inputs`, if the `kept` list is invalid (each `kept`
    /// `MetaVar` must from from the join key, or be found in exactly
    /// one input).
    ///
    /// Also returns `Err` when the number of inputs isn't two: we
    /// currently only support binary joins.
    pub fn join(
        inputs: Vec<Plan>,
        key: &[MetaVar],
        kept: &[MetaVar],
    ) -> Result<Self, &'static str> {
        JoinOp::make(inputs, key, kept)
    }

    /// Joins the input plans on their shared metavariables, while
    /// yielding the union of their metavariables.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the number of joined inputs isn't two: we
    /// currently only support binary joins.
    pub fn natural_join(inputs: Vec<Plan>) -> Result<Self, &'static str> {
        if inputs.len() != 2 {
            return Err("Only binary joins are currently supported.");
        }

        let input_vars: Vec<BTreeSet<MetaVar>> = inputs
            .iter()
            .map(|inp| inp.result.iter().cloned().collect())
            .collect();

        // The Join key is the intersection of the two inputs' variables.
        let key: Vec<_> = input_vars[0]
            .intersection(&input_vars[1])
            .cloned()
            .collect();
        // The result is the union of the two inputs' variables.  The
        // condition is more complex when there are more inputs: we
        // can "keep" a variable if it appears in the join key (is in
        // every input), or is in exactly one input.
        let kept: Vec<_> = input_vars[0].union(&input_vars[1]).cloned().collect();

        Self::join(inputs, &key, &kept)
    }

    /// Yields values from the minuend, minus any whose `key` matches
    /// the subtrahends.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the subtrahends' shape does not match `key`,
    /// or `key` cannot be constructed from the `minuend`'s shape.
    pub fn antijoin(
        minuend: Plan,
        key: &[MetaVar],
        subtrahends: Vec<Plan>,
    ) -> Result<Plan, &'static str> {
        AntijoinOp::make(minuend, key, subtrahends)
    }
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct FilterOp {
    source: Source,
    pattern: Vec<Element>,
}

impl FilterOp {
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn source(&self) -> &Source {
        &self.source
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn pattern(&self) -> &[Element] {
        &self.pattern
    }

    fn make(source: Source, pattern: &[Element]) -> Result<Plan, &'static str> {
        if source.arity != pattern.len() {
            return Err("Source predicate arity does not match pattern length.");
        }

        let parsed = Pattern::new(pattern)?;
        Ok(Plan {
            result: parsed.output().into(),
            op: PlanOp::Filter(FilterOp {
                source,
                pattern: pattern.into(),
            }),
        })
    }
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct ProjectOp {
    input: Box<Plan>,
}

impl ProjectOp {
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn input(&self) -> &Plan {
        &self.input
    }

    fn make(input: Plan, kept: &[MetaVar]) -> Result<Plan, &'static str> {
        let parsed = Projection::new(&input.result, kept)?;

        Ok(Plan {
            result: parsed.output().into(),
            op: PlanOp::Project(ProjectOp {
                input: Box::new(input),
            }),
        })
    }
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct JoinOp {
    inputs: Vec<Plan>,
    key: Vec<MetaVar>,
}

impl JoinOp {
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn inputs(&self) -> &[Plan] {
        &self.inputs
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn key(&self) -> &[MetaVar] {
        &self.key
    }

    fn make(inputs: Vec<Plan>, key: &[MetaVar], kept: &[MetaVar]) -> Result<Plan, &'static str> {
        if inputs.len() != 2 {
            return Err("Only binary joins are currently supported.");
        }

        // Normalise the join key.
        let join_key: BTreeSet<MetaVar> = key.iter().cloned().collect();

        let input_shapes: Vec<Box<[MetaVar]>> = inputs
            .iter()
            .map(|inp| inp.result.clone().into_boxed_slice())
            .collect();

        let parsed = MultiProjection::new(&input_shapes, kept)?;

        // Count the number of inputs in which each MetaVar appears:
        // we must make sure join keys are present in all inputs, and
        // other capture keys only present in one.
        let mut counts = HashMap::<MetaVar, usize>::new();
        for shape in &input_shapes {
            let unique: HashSet<MetaVar> = shape.iter().cloned().collect();
            for mv in unique.iter().cloned() {
                counts.entry(mv).and_modify(|x| *x += 1).or_insert(1);
            }
        }

        // Make sure the join `key` is present in every input.
        for mv in &join_key {
            if *counts.get(mv).unwrap_or(&0) != inputs.len() {
                return Err("Join key not present in all inputs.");
            }
        }

        // Make sure any value we keep that isn't in the join key
        // only appears in exactly one input.
        for mv in kept.iter() {
            if join_key.contains(mv) {
                continue;
            }

            match counts.get(mv) {
                None => return Err("Kept key absent from inputs"),
                Some(1) => (),
                Some(_) => return Err("Non-join kept key appears in many inputs"),
            }
        }

        Ok(Plan {
            result: parsed.output().into(),
            op: PlanOp::Join(JoinOp {
                inputs,
                key: join_key.iter().cloned().collect(),
            }),
        })
    }
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct AntijoinOp {
    minuend: Box<Plan>,
    key: Vec<MetaVar>,
    subtrahends: Vec<Plan>,
}

impl AntijoinOp {
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn minuend(&self) -> &Plan {
        &self.minuend
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn key(&self) -> &[MetaVar] {
        &self.key
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn subtrahends(&self) -> &[Plan] {
        &self.subtrahends
    }

    fn make(minuend: Plan, key: &[MetaVar], subtrahends: Vec<Plan>) -> Result<Plan, &'static str> {
        if subtrahends
            .iter()
            .any(|subtrahend| subtrahend.result() != key)
        {
            return Err("Subtrahend result shape does not match key.");
        }

        let key_set: BTreeSet<_> = key.iter().cloned().collect();
        if !key_set.is_subset(&minuend.result().iter().cloned().collect()) {
            return Err("Minuend result does not include match key.");
        }

        Ok(Plan {
            result: minuend.result().into(),
            op: PlanOp::Antijoin(AntijoinOp {
                minuend: Box::new(minuend),
                key: key.to_vec(),
                subtrahends,
            }),
        })
    }
}

#[test]
fn filter_happy_path() {
    let x = MetaVar::new("x");
    let source = Source::new("foo", 2);
    let pattern = [Element::Reference(x.clone()), Element::Reference(x.clone())];

    let filter = Plan::filter(source.clone(), &pattern).expect("ok");
    assert_eq!(filter.result(), &[x.clone()]);
}

#[test]
fn filter_mismatch() {
    let x = MetaVar::new("x");
    let source = Source::new("bar", 3);
    let pattern = [Element::Reference(x.clone()), Element::Reference(x.clone())];

    assert!(Plan::filter(source.clone(), &pattern).is_err());
}

#[test]
fn project_happy_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let source = Source::new("foo", 2);
    let pattern = [Element::Reference(x.clone()), Element::Reference(y.clone())];
    let filter = Plan::filter(source, &pattern).expect("ok");
    let project = Plan::project(filter, &[y.clone()]).expect("ok");
    assert_eq!(project.result(), &[y.clone()]);
}

#[test]
fn project_missing_var() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let source = Source::new("foo", 2);
    let pattern = [Element::Reference(y.clone()), Element::Reference(y.clone())];
    let filter = Plan::filter(source, &pattern).expect("ok");
    assert!(Plan::project(filter, &[x.clone()]).is_err());
}

#[test]
fn join_happy_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");

    let join = Plan::join(
        vec![f1, f2],
        &[y.clone()],
        &[x.clone(), y.clone(), z.clone()],
    )
    .expect("ok");
    assert_eq!(join.result(), &[x.clone(), y.clone(), z.clone()]);
}

#[test]
fn join_missing_join_var_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");

    assert!(Plan::join(
        vec![f1, f2],
        &[x.clone(), y.clone()],
        &[x.clone(), y.clone(), z.clone()],
    )
    .is_err());
}

#[test]
fn join_missing_result_var_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(y.clone()), Element::Reference(x.clone())],
    )
    .expect("ok");

    assert!(Plan::join(
        vec![f1, f2],
        &[x.clone(), y.clone()],
        &[x.clone(), y.clone(), z.clone()],
    )
    .is_err());
}

#[test]
fn join_non_binary_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);
    let s3 = Source::new("baz", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(z.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");
    let f3 = Plan::filter(
        s3,
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");

    assert!(Plan::join(
        vec![f1, f2, f3],
        &[x.clone(), y.clone()],
        &[x.clone(), y.clone(), z.clone()],
    )
    .is_err());
}

#[test]
fn join_bad_kept() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 3);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[
            Element::Reference(x.clone()),
            Element::Reference(y.clone()),
            Element::Reference(z.clone()),
        ],
    )
    .expect("ok");

    assert!(Plan::join(
        vec![f1, f2],
        &[x.clone()],
        &[x.clone(), y.clone(), z.clone()],
    )
    .is_err());
}

#[test]
fn antijoin_happy_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let s = Source::new("foo", 2);
    let minuend = Plan::filter(
        s.clone(),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let subtrahend = Plan::filter(
        s.clone(),
        &[Element::Reference(y.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");

    let antijoin = Plan::antijoin(minuend, &[y.clone()], vec![subtrahend]).expect("success");
    assert_eq!(antijoin.result(), vec![x.clone(), y.clone()]);
}

#[test]
fn antijoin_minuend_missing_key() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let s = Source::new("foo", 2);
    let minuend = Plan::filter(
        s.clone(),
        &[Element::Reference(x.clone()), Element::Reference(x.clone())],
    )
    .expect("ok");
    let subtrahend = Plan::filter(
        s.clone(),
        &[Element::Reference(y.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    assert!(Plan::antijoin(minuend, &[y.clone()], vec![subtrahend]).is_err());
}

#[test]
fn antijoin_subtrahend_missing_key() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let s = Source::new("foo", 2);
    let minuend = Plan::filter(
        s.clone(),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let subtrahend = Plan::filter(
        s.clone(),
        &[Element::Reference(x.clone()), Element::Reference(x.clone())],
    )
    .expect("ok");
    assert!(Plan::antijoin(minuend, &[y.clone()], vec![subtrahend]).is_err());
}

#[test]
fn antijoin_subtrahend_extra_key() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let s = Source::new("foo", 2);
    let minuend = Plan::filter(
        s.clone(),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let subtrahend = Plan::filter(
        s.clone(),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    assert!(Plan::antijoin(minuend, &[x.clone()], vec![subtrahend]).is_err());
}

#[test]
fn natural_join_happy_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");

    let join = Plan::natural_join(vec![f1, f2]).expect("ok");
    assert_eq!(join.result(), &[x.clone(), y.clone(), z.clone()]);
}

#[test]
fn natural_join_cross_product() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(z.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");

    let join = Plan::natural_join(vec![f1, f2]).expect("ok");
    assert_eq!(join.result(), &[x.clone(), y.clone(), z.clone()]);
}

#[test]
fn natural_join_incorrect() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let s1 = Source::new("foo", 2);
    let s2 = Source::new("bar", 2);
    let s3 = Source::new("baz", 2);

    let f1 = Plan::filter(
        s1,
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let f2 = Plan::filter(
        s2,
        &[Element::Reference(z.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");
    let f3 = Plan::filter(
        s3,
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");

    assert!(Plan::natural_join(vec![f1, f2, f3]).is_err());
}

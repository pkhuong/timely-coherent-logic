//! Given a Constraint, how do we want to apply filters, joins, and
//! project away data that isn't needed now that joins are done?
//!
//! There is no universally optimal answer to this question,
//! especially once we stop assuming binary joins.  Let's start with
//! operators that are trivial to express in Differential Dataflow,
//! and a criminally trivial plan.
use super::{Constraint, PredicateFormula};
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
}

/// Returns a Plan to match `constraint`, yielding capture tuples
/// that match the shape `constraint.captures()`.
pub fn plan_constraint(
    constraint: &Constraint,
    sources: &HashMap<String, Source>,
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
fn plan_formula(
    formula: &PredicateFormula,
    sources: &HashMap<String, Source>,
) -> Result<Plan, &'static str> {
    let source = sources
        .get(&formula.predicate)
        .ok_or("Predicate not found")?
        .clone();
    Plan::filter(source, &formula.pattern)
}

impl Plan {
    #[cfg(not(tarpaulin_include))]
    pub fn result(&self) -> &[MetaVar] {
        &self.result
    }

    #[cfg(not(tarpaulin_include))]
    pub fn op(&self) -> &PlanOp {
        &self.op
    }

    /// Constructs a plan that always yields an empty capture.
    pub fn constant() -> Result<Self, &'static str> {
        Ok(Plan {
            result: Vec::new(),
            op: PlanOp::Constant,
        })
    }

    /// Constructs a plan that returns captures in `pattern`, for
    /// tuples of `source` that match the pattern.
    pub fn filter(source: Source, pattern: &[Element]) -> Result<Self, &'static str> {
        FilterOp::make(source, pattern)
    }

    /// Constructs a plan that restructures the `input`'s tuples to
    /// match `kept`.
    pub fn project(input: Plan, kept: &[MetaVar]) -> Result<Self, &'static str> {
        ProjectOp::make(input, kept)
    }

    /// Constructs a plan that joins the `inputs`'s tuples that have
    /// equal values for `key`, and extracts `kept` metavars from the
    /// result.
    pub fn join(
        inputs: Vec<Plan>,
        key: &[MetaVar],
        kept: &[MetaVar],
    ) -> Result<Self, &'static str> {
        JoinOp::make(inputs, key, kept)
    }

    /// Joins the input plans on their shared metavariables, while
    /// yielding the union of their metavariables.
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
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct FilterOp {
    source: Source,
    pattern: Vec<Element>,
}

impl FilterOp {
    #[cfg(not(tarpaulin_include))]
    pub fn source(&self) -> &Source {
        &self.source
    }

    #[cfg(not(tarpaulin_include))]
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
    pub fn inputs(&self) -> &[Plan] {
        &self.inputs
    }

    #[cfg(not(tarpaulin_include))]
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
        for shape in input_shapes.iter() {
            let unique: HashSet<MetaVar> = shape.iter().cloned().collect();
            for mv in unique.iter().cloned() {
                counts.entry(mv).and_modify(|x| *x += 1).or_insert(1);
            }
        }

        // Make sure the join `key` is present in every input.
        for mv in join_key.iter() {
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

#[test]
fn filter_happy_path() {
    use crate::ground::Variable;

    let x = MetaVar::new("x");
    let source = Source::new("foo", 2);
    let pattern = [
        Element::Constant(Variable::new(1)),
        Element::Reference(x.clone()),
    ];

    let filter = Plan::filter(source.clone(), &pattern).expect("ok");
    assert_eq!(filter.result(), &[x.clone()]);
}

#[test]
fn filter_mismatch() {
    use crate::ground::Variable;

    let x = MetaVar::new("x");
    let source = Source::new("bar", 3);
    let pattern = [
        Element::Constant(Variable::new(1)),
        Element::Reference(x.clone()),
    ];

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
    use crate::ground::Variable;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let source = Source::new("foo", 2);
    let pattern = [
        Element::Constant(Variable::new(1)),
        Element::Reference(y.clone()),
    ];
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

#[test]
fn plan_constraint_smoke_test() {
    use super::Constraint;
    use super::PredicateFormula;

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

    let constraint = Constraint::new(BTreeSet::new(), Vec::new()).expect("ok");
    let sources = HashMap::new();
    let plan = plan_constraint(&constraint, &sources).expect("ok");

    assert_eq!(plan.result(), &[]);
}

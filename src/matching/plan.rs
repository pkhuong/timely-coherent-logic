//! Given a Constraint, how do we want to apply filters, joins, and
//! project away data that isn't needed now that joins are done?
//!
//! There is no universally optimal answer to this question,
//! especially once we stop assuming binary joins.  Let's start with
//! operators that are trivial to express in Differential Dataflow,
//! and a criminally trivial plan.
use crate::unification::{Element, MetaVar, Pattern, Projection};

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

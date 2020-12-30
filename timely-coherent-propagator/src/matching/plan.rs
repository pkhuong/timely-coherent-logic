//! Given a Constraint, how do we want to apply filters, joins, and
//! project away data that isn't needed now that joins are done?  The
//! data structures defined in this module describe a planning
//! function's answer to that question.
//!
//! For the foreseeable future, we will stick to nodes that can be
//! directly translated to differential dataflow operators.
use crate::unification::MetaVar;

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
}

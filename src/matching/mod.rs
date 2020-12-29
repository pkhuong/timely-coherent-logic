//! The core of a Coherent Logic (CL) solver is pattern matching on
//! rules of the form $$\forall x, y, z: p(x, y) \wedge q(y, z) \wedge ... =>
//! ...$$ This work builds on `unification::Pattern` to match against
//! multiple facts at once.  We will use this pattern matching to find
//! potential instantiation parameters for the right-hand side of the
//! $$=>$$ implication, but also to detect when some instantiation are
//! useless.
//!
//! The right-hand side of the implication is a disjunction of
//! conjunctions; if any of these conjunctions is already true, the
//! implication has no logical relevance (for all corresponding
//! parameters).  CL also lets disjunctions on the right-hand side
//! introduce new variables, with terms like $$\exists a: r(a, x) \wedge
//! s(x, y),$$ where some metavariables were bound by matching in the
//! left-hand side, and others introduced by $$\exists,$$ and
//! substituted with fresh variables when instantiated.
//!
//! A key subtlety in CL is that, as long as we can find tuples that
//! match $$r(a, x) \wedge s(x, y),$$ the existential expression is
//! already satisfied, and all corresponding instances of the
//! implications are irrelevant.  Detecting that after the fact
//! in a relational fashion seems non-trivial; we'll instead match
//! on all conjunctions in the right-hand-side, and antijoin with
//! current matches.
//!
//! The execution of matching happens in two phases.  We first
//! generate an expression tree to describes the steps we'll need to
//! convert Collections of facts (one per predicate) to a Collection
//! of matches.  Then, we convert that expression tree to a Collection
//! processing expression.  The indirection seems like spurious
//! complexity at first, but having a concrete representation for the
//! matching expression helps introduce rewrites (e.g., local
//! heuristic transforms or global tree parsing), and is also useful
//! for debugging.
mod expression;

pub use expression::Constraint;
pub use expression::PredicateFormula;

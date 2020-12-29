//! An implementation of Coherent Logic never needs full unification:
//! either we're matching a pattern against a fully ground value, or
//! fully instantiating a template with an environment.  In order to
//! drive joins (i.e., to implement patterns that span multiple
//! predicates), we must also implement environment restructuring.
//! Matching accepts facts, and returns a substitution (a pair of
//! captured variables and corresponding metavariables) on success.
//! Restructuring accepts a substitution (or multiple substitutions),
//! and returns another substitution.
//!
//! The usual split between static shape and dynamic variables
//! pervades our implementations of matching and restructuring. The
//! transformation or matching we wish to perform is a function of the
//! axioms and query plan, but not of the data; it makes sense to
//! front-load as much work as possible before traversing containers,
//! especially in the differential dataflow world, where containers
//! are updated incrementally.
mod metavariable;
mod pattern;
mod project;

pub use metavariable::MetaVar;
pub use pattern::instantiate_template;
pub use pattern::Element;
pub use pattern::Pattern;
pub use pattern::Template;
pub use project::MultiProjection;
pub use project::Projection;

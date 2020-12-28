//! The Timely Coherent Logic prover starts with a database of known
//! facts, and incrementally adds new facts as they are derived.
//! These facts are "ground" formulas involving only opaque variables
//! and constant (named) predicates.  The core of the prover
//! manipulates variables, more precisely lists of variables, and
//! these lists of variables will constitute the bulk of what we store
//! in Collections.  Our ground data structures must thus be as light
//! as possible, while offering fast hashing and comparison.

mod variable;

pub use variable::Variable;

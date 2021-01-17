//! Traits and types that represent Satumerator's knowledge of the
//! search space.
use std::fmt::Debug;
use std::hash::Hash;

/// A `StateAtom` is an atomic piece of state, e.g., the decision `x =
/// true`.
pub trait StateAtom
where
    Self: Clone + Debug + Eq + Hash + PartialOrd + Ord + Sized,
{
}

// `String`s trivially implement `StateAtom`.
impl StateAtom for String {}

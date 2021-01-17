//! Traits and types that represent Satumerator's knowledge of the
//! search space.
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::Hash;

/// A `StateAtom` is an atomic piece of state, e.g., the decision `x =
/// true`.
pub trait StateAtom
where
    Self: Clone + Debug + Eq + Hash + PartialOrd + Ord + Sized,
{
}

/// A `FathomedRegion` represents the knowledge that we have fully
/// explored all states that match `partial_assignment`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FathomedRegion<A: StateAtom> {
    pub partial_assignment: BTreeSet<A>,
}

/// A `ChoiceConstraint` is a set of `StateAtoms` from which any valid
/// state much pick exactly one option to assert as true.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ChoiceConstraint<A: StateAtom> {
    pub options: BTreeSet<A>,
}

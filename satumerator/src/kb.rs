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

// `String`s trivially implement `StateAtom`.
impl StateAtom for String {}

/// A `FathomedRegion` represents the knowledge that we have fully
/// explored all states that match `partial_assignment`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FathomedRegion<A: StateAtom> {
    pub partial_assignment: BTreeSet<A>,
}

impl<A: StateAtom> FathomedRegion<A> {
    /// Returns a `FathomedRegion` for all the atoms in the iteratable `atoms`.
    pub fn new<Iter>(atoms: Iter) -> Self
    where
        Iter: IntoIterator<Item = A>,
    {
        Self {
            partial_assignment: atoms.into_iter().collect::<BTreeSet<_>>(),
        }
    }
}

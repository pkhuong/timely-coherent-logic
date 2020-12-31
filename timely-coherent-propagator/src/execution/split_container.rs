//! Planning and executing matching queries on differential
//! Collections is too dynamic for a non-dependent type system like
//! Rust's.  Rather than try to play fancy type-level tricks, we track
//! the shape of input data dynamically.  Of course, doing so for each
//! item in a collection would be inefficient and error-prone (it's
//! far too easy to hide type mismatches in empty collections).
//!
//! Split collections are simple wrappers around differential dataflow
//! Collections, tagged with the shape of all their constituent items.
//! This static / dynamic split lets us check compatibility as we
//! construct the dataflow graph, rather than once per items.
use crate::ground::{Capture, Fact};
use crate::unification::MetaVar;
use differential_dataflow::collection::Collection;
use differential_dataflow::input::InputSession;
use differential_dataflow::operators::iterate::Variable;

/// A `FactCollection` is a `Collection` of `ground::Fact`s, all of
/// the same length.
pub type FactCollection<G, R = isize> = SplitCollection<G, usize, Fact, R>;

/// A `FactInput` is an `InputSession` of `ground::Fact`s of the same
/// shape.
pub type FactInput<T, R = isize> = SplitInput<T, usize, Fact, R>;

/// A `FactVariable` is the same as a `FactCollection`, but with facts
/// stored in an `iterate::Variable`.
pub type FactVariable<G, R = isize> = SplitVariable<G, usize, Fact, R>;

/// A `CaptureCollection` is a `Collection` of `ground::Capture`s, all
/// matching the same list of `MetaVar`s.
pub type CaptureCollection<G, R = isize> = SplitCollection<G, Vec<MetaVar>, Capture, R>;

/// A `CaptureInput` is an `InputSession` of `group::Capture`s of the
/// same shape.
pub type CaptureInput<T, R = isize> = SplitInput<T, Vec<MetaVar>, Capture, R>;

/// A `CaptureVariable` is the same as a `CaptureCollection`, but with
/// `Capture`s stored in an `iterate::Variable`.
pub type CaptureVariable<G, R = isize> = SplitVariable<G, Vec<MetaVar>, Capture, R>;

/// A `SplitCollection` is a shape-tagged DD `Collection`.
pub type SplitCollection<G, S, D, R = isize> = SplitContainer<S, Collection<G, D, R>>;

/// A `SplitInput` is a shape-tagged DD `InputSession`.
pub type SplitInput<T, S, D, R = isize> = SplitContainer<S, InputSession<T, D, R>>;

/// A `SplitVariable` is a shape-tagged DD iteration (cyclic) `Variable`.
pub type SplitVariable<G, S, D, R = isize> = SplitContainer<S, Variable<G, D, R>>;

pub struct SplitContainer<Shape, Container> {
    pub shape: Shape,
    pub container: Container,
}

impl<Shape, Container> SplitContainer<Shape, Container> {
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn new(shape: Shape, container: Container) -> Self {
        Self { shape, container }
    }
}

impl<S: Clone, C: Clone> Clone for SplitContainer<S, C> {
    #[cfg(not(tarpaulin_include))]
    fn clone(&self) -> Self {
        Self {
            shape: self.shape.clone(),
            container: self.container.clone(),
        }
    }
}

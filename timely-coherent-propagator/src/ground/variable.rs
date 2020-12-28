//! Coherent Logic is a special case of first-order logic, and thus
//! manipulates opaque variables adorned only with an opaque identity.
//!
//! While we may eventually wish to annotate variables with type
//! information, such information should be tracked at a higher level:
//! we expect to store variables in collections, where every value in
//! each collection has the same shape.  Hoisting the shape
//! information out of each such collection helps us save space and
//! time, as well as detect mismatches early.

/// A concrete variable is simply a machine integer.  We should only
/// introduce new variables for initial axioms, or at choice points,
/// and the latter should be rare (otherwise performance is guaranteed
/// to be awful).  32-bit integers should be more than enough.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable(u32);

impl Variable {
    /// Returns a fresh unique variable.
    #[must_use]
    pub fn fresh() -> Self {
        #[cfg(not(tarpaulin_include))]
        fn id() -> u32 {
            use std::sync::atomic;
            static COUNTER: atomic::AtomicU32 = atomic::AtomicU32::new(1);

            COUNTER.fetch_add(1, atomic::Ordering::Relaxed)
        }

        Self::new(id())
    }

    /// A new variable must have a non-negative index: we use 0 as a
    /// sentinel.
    #[must_use]
    pub fn new(id: u32) -> Self {
        assert!(id > 0);
        // TODO: apply a reversible bit mixer here in order, in order
        // to make hashing as trivial as possible.
        Self(id)
    }

    /// Returns a sentinel Variable value.
    #[inline]
    #[must_use]
    pub fn uninit() -> Self {
        Self(0)
    }

    /// Returns true iff `self` is a sentinel `uninit` value.
    #[inline]
    #[must_use]
    pub fn is_uninit(self) -> bool {
        self.0 == 0
    }
}

#[test]
fn test_fresh() {
    assert_ne!(Variable::fresh(), Variable::fresh());
}

#[test]
fn test_uninit() {
    assert_eq!(Variable::uninit(), Variable::uninit());
    assert!(Variable::uninit().is_uninit());
    assert!(!Variable::new(1).is_uninit());
    assert!(!Variable::fresh().is_uninit());
}

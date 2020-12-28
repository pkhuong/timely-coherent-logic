/// A metavariable is a name for, e.g., a bound variable in $$\forall x$$.
///
/// Metavariables are uniquely identified by their sequence id; the
/// name itself is only useful for pretty-printing.
///
/// The implicit order on metavariables sorts by sequence id
/// (ascending).  This order should naturally do what one expects for
/// hierarchies, as long as metavariables are generated with a
/// pre-order depth-first traversal.
#[derive(Clone, Debug, Eq)]
pub struct MetaVar {
    sequence: usize,
    name: String,
}

impl MetaVar {
    /// Returns a new MetaVar with `name`.
    pub fn new(name: &str) -> Self {
        #[cfg(not(tarpaulin_include))]
        fn id() -> usize {
            use std::sync::atomic::{AtomicUsize, Ordering};
            static METAVAR_COUNTER: AtomicUsize = AtomicUsize::new(0);

            METAVAR_COUNTER.fetch_add(1, Ordering::Relaxed)
        }

        Self {
            sequence: id(),
            name: name.into(),
        }
    }
}

impl std::hash::Hash for MetaVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.sequence.hash(state);
    }
}

impl PartialEq for MetaVar {
    fn eq(&self, other: &Self) -> bool {
        self.sequence == other.sequence
    }
}

impl PartialOrd for MetaVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MetaVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sequence.cmp(&other.sequence)
    }
}

#[test]
fn test_smoke() {
    let mv0 = MetaVar::new("zxc");
    let mv1 = MetaVar::new("asd");

    assert!(mv0 < mv1);
    assert_ne!(mv0, mv1);
}

#[test]
fn test_eq_hash() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hash;
    use std::hash::Hasher;

    let mv0 = MetaVar::new("a");
    let mv0_clone = mv0.clone();
    // mv0 and mv1 should be distinct, despite their name.
    let mv1 = MetaVar::new("a");

    assert_eq!(mv0, mv0_clone);
    assert_ne!(mv0, mv1);

    {
        let mut h0 = DefaultHasher::new();
        let mut h1 = DefaultHasher::new();

        mv0.hash(&mut h0);
        mv1.hash(&mut h1);
        assert_ne!(h0.finish(), h1.finish());
    }

    {
        let mut h0 = DefaultHasher::new();
        let mut h0_clone = DefaultHasher::new();

        mv0.hash(&mut h0);
        mv0_clone.hash(&mut h0_clone);

        assert_eq!(h0.finish(), h0_clone.finish());
    }
}

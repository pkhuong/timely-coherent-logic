//! Differential Dataflow collections are closer to pipes that
//! describe a computation's dataflow than to concrete collections.
//! In order to get data out of a DD computation, we must listen to a
//! collection's change stream, and reify the result into the
//! collection we want.
//!
//! The sink interface looks a bit weird, with the write end fully
//! decoupled from the read (snapshot) end; that's because we want
//! to write from a worker thread, so must pass ownership of the
//! write end to a closure.
use super::split_containers::SplitCollection;
use crate::ground::{Capture, Fact};
use crate::unification::MetaVar;
use differential_dataflow::difference::Semigroup;
use differential_dataflow::Data;
use std::collections::HashMap;
use std::hash::Hash;
use timely::dataflow::Scope;

pub type CaptureSink = Sink<Vec<MetaVar>, Capture>;
pub type CaptureWriter = SinkWriter<Vec<MetaVar>, Capture>;
pub type FactSink = Sink<usize, Fact>;
pub type FactWriter = SinkWriter<usize, Fact>;

/// A Sink accepts data of a certain type and shape, and exposes a
/// running multiplicity snapshot for all the data it has received
/// (so far) from differential dataflow collections.
///
/// In order to hook up a collection to a Sink, one must first gain
/// ownership of a `SinkWriter`, by calling `Sink::writer()`.
#[derive(Clone, Debug)]
pub struct Sink<S: 'static + Clone + Eq, D: Data + Eq + Hash, R: Semigroup = isize> {
    inner: std::sync::Arc<SinkImpl<S, D, R>>,
}

impl<S: 'static + Clone + Eq, D: Data + Eq + Hash, R: Semigroup> Sink<S, D, R> {
    pub fn new(shape: S) -> Self {
        Self {
            inner: std::sync::Arc::new(SinkImpl::new(shape)),
        }
    }

    /// Returns the shape of each item written to the sink.
    #[cfg(not(tarpaulin_include))]
    pub fn shape(&self) -> &S {
        &self.inner.shape
    }

    /// Returns a fresh writer for the sink.
    pub fn writer(&self) -> SinkWriter<S, D, R> {
        SinkWriter {
            inner: self.inner.clone(),
        }
    }

    /// Collects all the values with non-zero multiplicities.
    pub fn values<Ret: std::iter::FromIterator<D>>(&self) -> Ret {
        self.with_snapshot(|map| map.keys().cloned().collect())
    }

    /// Calls `handler` with a snapshot of the data in the sink.  The
    /// key in the map is the data, and the value its multiplicity.
    /// There will never be a zero-valued entry, so it is safe to, e.g.,
    /// only look at the map's keys.
    pub fn with_snapshot<F, Ret>(&self, handler: F) -> Ret
    where
        F: FnOnce(&HashMap<D, R>) -> Ret,
    {
        self.inner.with_snapshot(handler)
    }
}

#[derive(Clone, Debug)]
pub struct SinkWriter<S: 'static + Clone + Eq, D: Data + Eq + Hash, R: Semigroup = isize> {
    inner: std::sync::Arc<SinkImpl<S, D, R>>,
}

impl<S: 'static + Clone + Eq, D: Data + Eq + Hash, R: Semigroup> SinkWriter<S, D, R> {
    /// Attaches an `inspect`or closure to the collection's underlying
    /// DD collection; the `Sink`'s state will be updated to reflect
    /// the multiplicity of the data in that collection.
    ///
    /// If the same sink is attached to multiple collections, it is
    /// equivalent to attaching it to the concatenation of these
    /// collections.
    pub fn attach<G: Scope>(
        &self,
        collection: &SplitCollection<G, S, D, R>,
    ) -> Result<(), &'static str> {
        SinkImpl::attach(self.inner.clone(), collection)
    }
}

#[derive(Debug)]
struct SinkImpl<S: 'static + Clone + Eq, D: Data + Eq + Hash, R: Semigroup = isize> {
    shape: S,
    counts: std::sync::Mutex<HashMap<D, R>>,
}

impl<S: 'static + Clone + Eq, D: Data + Eq + Hash, R: Semigroup> SinkImpl<S, D, R> {
    fn new(shape: S) -> Self {
        Self {
            shape,
            counts: std::sync::Mutex::new(HashMap::new()),
        }
    }

    fn with_snapshot<F, Ret>(&self, handler: F) -> Ret
    where
        F: FnOnce(&HashMap<D, R>) -> Ret,
    {
        let counts = self.counts.lock().unwrap();
        handler(&counts)
    }

    pub fn attach<G: Scope>(
        this: std::sync::Arc<Self>,
        collection: &SplitCollection<G, S, D, R>,
    ) -> Result<(), &'static str> {
        if collection.shape != this.shape {
            return Err("Unexpected collection shape for sink.");
        }

        collection.container.inspect(move |(data, _time, diff)| {
            let mut counts = this.counts.lock().unwrap();
            if counts
                .entry(data.clone())
                .and_modify(|acc| *acc += diff)
                .or_insert_with(|| diff.clone())
                .is_zero()
            {
                counts.remove(data);
            }
        });
        Ok(())
    }
}

#[test]
fn test_happy_path() {
    use super::FactCollection;
    use crate::ground::Fact;
    use crate::ground::Variable;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let sink = FactSink::new(1);
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();

        let source = FactCollection::new(1, foo.to_collection(scope));
        writer.attach(&source).expect("ok");

        foo.advance_to(0);
        for i in 1..10 {
            foo.insert([Variable::new(i)].into());
        }

        foo.flush();
        foo.advance_to(1);
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        (1..10)
            .map(|i| Fact::from_slice(&[Variable::new(i)]))
            .collect()
    );
}

#[test]
fn test_multi_counts() {
    use super::FactCollection;
    use crate::ground::Variable;
    use differential_dataflow::input::InputSession;

    let sink = FactSink::new(1);
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();

        let source = FactCollection::new(1, foo.to_collection(scope));
        writer.attach(&source).expect("ok");

        foo.advance_to(0);
        foo.insert([Variable::new(1)].into());
        foo.insert([Variable::new(2)].into());
        foo.insert([Variable::new(3)].into());
        foo.flush();
        foo.advance_to(1);
        foo.insert([Variable::new(1)].into());
        foo.remove([Variable::new(3)].into());
        foo.remove([Variable::new(4)].into());
        foo.flush();
        foo.advance_to(2);
    });

    assert_eq!(
        sink.with_snapshot(|map| map.clone()),
        [
            ([Variable::new(1)].into(), 2),
            ([Variable::new(2)].into(), 1),
            ([Variable::new(4)].into(), -1),
        ]
        .iter()
        .cloned()
        .collect()
    );
}

#[test]
fn test_mismatch_path() {
    use super::FactCollection;
    use differential_dataflow::input::InputSession;

    let sink = FactSink::new(2);
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();

        let source = FactCollection::new(1, foo.to_collection(scope));
        assert!(writer.attach(&source).is_err());
    });
}

//! Lowering a plan converts a [Plan](crate::matching::Plan) to a
//! differential dataflow graph.
use super::{CaptureCollection, FactCollection};
use crate::ground::Capture;
use crate::matching::plan::FilterOp;
use crate::matching::plan::Plan;
use crate::unification;
use crate::unification::MetaVar;
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::Collection;
use timely::dataflow::Scope;

/// This function may be used as the `injector` argument to
/// `lower_matching_plan`, when `scope` is a differential dataflow top
/// level.
pub fn default_injector<G: Input>(scope: &mut G, initial: Vec<Capture>) -> Collection<G, Capture> {
    scope.new_collection_from(initial).1
}

/// Recursively converts a matching plan to a differential dataflow
/// graph.
///
/// The `injector` must be a callable that accepts `scope` and vector
/// of values, and returns a collection for `scope` initialised with
/// these values.  This injector will be called with very few distinct
/// vectors; memoisation or caching is probably a good idea.
///
/// # Errors
///
/// Returns `Err` when the `inputs`'s shapes do not match the plan's
/// `Source`s.
pub fn lower_matching_plan<G: Scope, Injector, H: std::hash::BuildHasher>(
    scope: &mut G,
    injector: &mut Injector,
    plan: &Plan,
    inputs: &std::collections::HashMap<String, FactCollection<G>, H>,
) -> Result<CaptureCollection<G>, &'static str>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    use crate::matching::plan::PlanOp::{Constant, Filter};

    let planned_shape = plan.result();
    let result = match plan.op() {
        Constant => lower_constant(scope, injector, inputs),
        Filter(op) => lower_filter(scope, injector, op, inputs),
    }?;

    // If the result's shape does not match the plan, something went
    // horribly wrong.
    assert_eq!(planned_shape, result.shape);
    Ok(result)
}

type FactMap<G, H> = std::collections::HashMap<String, FactCollection<G>, H>;
type PlanResult<G> = Result<CaptureCollection<G>, &'static str>;

/// A constant node always yields a nullary capture tuple.
fn lower_constant<G: Scope, Injector, H: std::hash::BuildHasher>(
    scope: &mut G,
    injector: &mut Injector,
    _inputs: &FactMap<G, H>,
) -> PlanResult<G>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    Ok(CaptureCollection::new(
        vec![],
        injector(scope, vec![Capture::from_slice(&[])]),
    ))
}

/// A filter stage selects fact records that match the pattern, and
/// yields captures for successful matches.
fn lower_filter<G: Scope, Injector, H: std::hash::BuildHasher>(
    _scope: &G,
    _injector: &mut Injector,
    op: &FilterOp,
    inputs: &FactMap<G, H>,
) -> PlanResult<G>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    let planned_source = op.source();
    let pattern = unification::Pattern::new(op.pattern())?;
    let source = inputs
        .get(&planned_source.predicate_name)
        .ok_or("Source predicate not found.")?;
    let shape: Vec<MetaVar> = pattern.output().into();

    // This invariant is enforced when constructing the plan.
    assert!(pattern.input_len() == planned_source.arity);

    if source.shape != planned_source.arity {
        return Err("Source predicate shape does not match plan.");
    }

    let collection = source
        .container
        .flat_map(move |fact| pattern.try_match(&fact));
    Ok(CaptureCollection::new(shape, collection))
}

#[test]
fn test_constant_happy_path() {
    use super::CaptureSink;
    use std::collections::HashSet;

    let constant = Plan::constant().expect("ok");

    let sink = CaptureSink::new(constant.result().into());
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let sources = FactMap::new();

        let captures =
            lower_matching_plan(scope, &mut default_injector, &constant, &sources).expect("ok");
        writer.attach(&captures).expect("ok");
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        [[].into()].iter().cloned().collect()
    );
}

#[test]
fn test_filter_happy_path() {
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let source = Source::new("foo", 2);

    let pattern = [Element::Reference(x.clone()), Element::Reference(x.clone())];
    let filter = Plan::filter(source.clone(), &pattern).expect("ok");

    let sink = CaptureSink::new(filter.result().into());
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();

        let sources = vec![(
            "foo".into(),
            FactCollection::new(2, foo.to_collection(scope)),
        )]
        .into_iter()
        .collect::<std::collections::HashMap<String, _>>();

        let captures =
            lower_matching_plan(scope, &mut default_injector, &filter, &sources).expect("ok");
        writer.attach(&captures).expect("ok");

        foo.advance_to(0);
        for i in 1..10 {
            if (i % 2) == 0 {
                foo.insert([Variable::new(i), Variable::new(i)].into());
            } else {
                foo.insert([Variable::new(i), Variable::new(i + 1)].into());
            }
        }

        foo.flush();
        foo.advance_to(1);
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        [2, 4, 6, 8]
            .iter()
            .map(|i| [Variable::new(*i)].into())
            .collect()
    );
}

#[test]
fn test_filter_missing_source() {
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;

    let x = MetaVar::new("x");
    let source = Source::new("foo", 2);

    let pattern = [Element::Reference(x.clone()), Element::Reference(x.clone())];
    let filter = Plan::filter(source.clone(), &pattern).expect("ok");

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();

        let sources = vec![(
            "bar".into(),
            FactCollection::new(2, foo.to_collection(scope)),
        )]
        .into_iter()
        .collect::<std::collections::HashMap<String, _>>();

        assert!(lower_matching_plan(scope, &mut default_injector, &filter, &sources).is_err());
    });
}

#[test]
fn test_filter_incorrect_source_source() {
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;

    let x = MetaVar::new("x");
    let source = Source::new("foo", 2);

    let pattern = [Element::Reference(x.clone()), Element::Reference(x.clone())];
    let filter = Plan::filter(source.clone(), &pattern).expect("ok");

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();

        let sources = vec![(
            "foo".into(),
            FactCollection::new(3, foo.to_collection(scope)),
        )]
        .into_iter()
        .collect::<std::collections::HashMap<String, _>>();

        assert!(lower_matching_plan(scope, &mut default_injector, &filter, &sources).is_err());
    });
}

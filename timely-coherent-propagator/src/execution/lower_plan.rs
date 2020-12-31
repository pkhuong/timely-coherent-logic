//! Lowering a plan converts a [Plan](crate::matching::Plan) to a
//! differential dataflow graph.
use super::{CaptureCollection, FactCollection};
use crate::ground::Capture;
use crate::matching::plan::Plan;
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
    use crate::matching::plan::PlanOp::Constant;

    let planned_shape = plan.result();
    let result = match plan.op() {
        Constant => lower_constant(scope, injector, inputs),
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

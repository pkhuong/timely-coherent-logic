//! Lowering a plan converts a [Plan](crate::matching::Plan) to a
//! differential dataflow graph.
use super::{CaptureCollection, FactCollection};
use crate::ground::Capture;
use crate::matching::plan::*;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::Collection;
use timely::dataflow::Scope;

/// Recursively converts a matching plan to a differential dataflow
/// graph.
///
/// The `injector` must be a callable that accepts `scope` and vector
/// of values, and returns a collection for `scope` initialised with
/// these values.  This injector will be called with very few distinct
/// vectors; memoisation or caching is probably a good idea.
pub fn lower_matching_plan<G: Scope, Injector>(
    scope: &mut G,
    injector: &mut Injector,
    plan: &Plan,
    inputs: &std::collections::HashMap<String, FactCollection<G>>,
) -> Result<CaptureCollection<G>, &'static str>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    use crate::matching::plan::PlanOp::*;

    let planned_shape = plan.result();
    let result = match plan.op() {
        Constant => lower_constant(scope, injector, inputs),
    }?;

    // If the result's shape does not match the plan, something went
    // horribly wrong.
    assert_eq!(planned_shape, result.shape);
    Ok(result)
}

type FactMap<G> = std::collections::HashMap<String, FactCollection<G>>;
type PlanResult<G> = Result<CaptureCollection<G>, &'static str>;

/// A constant node always yields a nullary capture tuple.
fn lower_constant<G: Scope, Injector>(
    scope: &mut G,
    injector: &mut Injector,
    _inputs: &FactMap<G>,
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
    use differential_dataflow::input::Input;
    use std::collections::HashSet;

    let constant = Plan::constant().expect("ok");

    let sink = CaptureSink::new(constant.result().into());
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let sources = FactMap::new();

        let captures = lower_matching_plan(
            scope,
            &mut |scope, values| scope.new_collection_from(values).1,
            &constant,
            &sources,
        )
        .expect("ok");
        writer.attach(&captures).expect("ok");
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        [[].into()].iter().cloned().collect()
    );
}

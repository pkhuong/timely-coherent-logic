//! Lowering a plan converts a [Plan](crate::matching::Plan) to a
//! differential dataflow graph.
use super::{CaptureCollection, FactCollection};
use crate::ground::Capture;
use crate::matching::plan::AntijoinOp;
use crate::matching::plan::FilterOp;
use crate::matching::plan::JoinOp;
use crate::matching::plan::Plan;
use crate::matching::plan::ProjectOp;
use crate::unification;
use crate::unification::MetaVar;
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::operators::Join;
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
    use crate::matching::plan::PlanOp::{Antijoin, Constant, Filter, Join, Project};

    let planned_shape = plan.result();
    let result = match plan.op() {
        Constant => lower_constant(scope, injector, inputs),
        Filter(op) => lower_filter(scope, injector, op, inputs),
        Project(op) => lower_project(scope, injector, planned_shape, op, inputs),
        Join(op) => lower_join(scope, injector, planned_shape, op, inputs),
        Antijoin(op) => lower_antijoin(scope, injector, op, inputs),
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

/// A projection stage rearranges (reorders, copies, or drops)
/// variables from a collection of captures.
fn lower_project<G: Scope, Injector, H: std::hash::BuildHasher>(
    scope: &mut G,
    injector: &mut Injector,
    kept: &[MetaVar],
    op: &ProjectOp,
    inputs: &FactMap<G, H>,
) -> PlanResult<G>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    let input = lower_matching_plan(scope, injector, op.input(), inputs)?;
    let project = unification::Projection::new(&input.shape, kept)?;
    let shape: Vec<MetaVar> = project.output().into();

    Ok(CaptureCollection::new(
        shape,
        input.container.map(move |fact| project.apply(&fact)),
    ))
}

/// In order to join two collections on a join key, we must extract
/// the join key values from each, let differential dataflow pair up
/// entries with identical join keys from each collection, and extract
/// the metavariables we want from each pair of matching captures.
fn lower_join<G: Scope, Injector, H: std::hash::BuildHasher>(
    scope: &mut G,
    injector: &mut Injector,
    kept: &[MetaVar],
    op: &JoinOp,
    inputs: &FactMap<G, H>,
) -> PlanResult<G>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    // We only support binary joins for now (enforced in the
    // constructor).
    assert!(op.inputs().len() == 2);

    let join_key = op.key();
    let input_nodes = op
        .inputs()
        .iter()
        .map(|plan| lower_matching_plan(scope, injector, plan, inputs))
        .collect::<Result<Vec<_>, _>>()?;

    let tagged_inputs = input_nodes
        .iter()
        .map(|collection| {
            let projection = unification::Projection::new(&collection.shape, join_key)?;
            Ok(collection
                .container
                .map(move |capture| (projection.apply(&capture), capture)))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let final_projection = unification::MultiProjection::new(
        &input_nodes
            .iter()
            .map(|split| split.shape.clone().into_boxed_slice())
            .collect::<Vec<_>>(),
        kept,
    )?;

    let final_shape: Vec<MetaVar> = final_projection.output().into();
    let collection = tagged_inputs[0].join_map(&tagged_inputs[1], move |_key, x, y| {
        final_projection.from_pair(x, y)
    });
    Ok(CaptureCollection::new(final_shape, collection))
}

fn lower_antijoin<G: Scope, Injector, H: std::hash::BuildHasher>(
    scope: &mut G,
    injector: &mut Injector,
    op: &AntijoinOp,
    inputs: &FactMap<G, H>,
) -> PlanResult<G>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    use differential_dataflow::collection::concatenate;
    use differential_dataflow::operators::Threshold;

    // All the subtrahends must have exactly the same shape as the
    // antijoin key.
    let subtrahend_nodes = op
        .subtrahends()
        .iter()
        .map(|plan| lower_matching_plan(scope, injector, plan, inputs))
        .collect::<Result<Vec<_>, _>>()?;

    // This condition is checked in the plan constructor.
    if subtrahend_nodes.iter().any(|node| node.shape != op.key()) {
        #[cfg(not(tarpaulin_include))]
        return Err("Subtrahend shape does not match antijoin key.");
    }

    let minuend_node = lower_matching_plan(scope, injector, op.minuend(), inputs)?;

    // Make sure we can extract the antijoin key from the minuend's data.
    let project = unification::Projection::new(&minuend_node.shape, op.key())?;

    // We'll want to remove any record in `minuend` that matches at
    // least one of the subtrahends.  Given the semantics of antijoin
    // (minuend_count -= subtrahend_count * minuend_count), we want
    // to apply `distinct()` before antijoining.
    let merged_subtrahend = concatenate(
        scope,
        subtrahend_nodes.into_iter().map(|node| node.container),
    )
    .distinct();

    // Tag each of the minuend's records with its projected join key.
    let minuend = minuend_node
        .container
        .map(move |record| (project.apply(&record), record));

    // Take the difference, and untag.
    let difference = minuend.antijoin(&merged_subtrahend).map(|tagged| tagged.1);

    Ok(CaptureCollection::new(minuend_node.shape, difference))
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

#[test]
fn test_project_happy_path() {
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let source = Source::new("foo", 2);

    let pattern = [Element::Reference(x.clone()), Element::Reference(y.clone())];
    let filter = Plan::filter(source.clone(), &pattern).expect("ok");
    let project = Plan::project(filter, &[y.clone()]).expect("ok");

    let sink = CaptureSink::new(project.result().into());
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
            lower_matching_plan(scope, &mut default_injector, &project, &sources).expect("ok");
        writer.attach(&captures).expect("ok");

        foo.advance_to(0);
        for i in 1..5 {
            foo.insert([Variable::new(i), Variable::new(2 * i)].into());
            foo.insert([Variable::new(i), Variable::new(2 * i + 1)].into());
        }

        foo.flush();
        foo.advance_to(1);
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        (2..10).map(|i| [Variable::new(i)].into()).collect()
    );
}

#[test]
fn test_join_happy_path() {
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let p1 = Plan::filter(
        Source::new("foo", 2),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let p2 = Plan::filter(
        Source::new("bar", 2),
        &[Element::Reference(y.clone()), Element::Reference(z.clone())],
    )
    .expect("ok");
    let join = Plan::join(
        vec![p1, p2],
        &[y.clone()],
        &[x.clone(), y.clone(), z.clone()],
    )
    .expect("ok");

    let sink = CaptureSink::new(join.result().into());
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();
        let mut bar = InputSession::new();

        let sources = vec![
            (
                "foo".into(),
                FactCollection::new(2, foo.to_collection(scope)),
            ),
            (
                "bar".into(),
                FactCollection::new(2, bar.to_collection(scope)),
            ),
        ]
        .into_iter()
        .collect::<std::collections::HashMap<String, _>>();

        let captures =
            lower_matching_plan(scope, &mut default_injector, &join, &sources).expect("ok");
        writer.attach(&captures).expect("ok");

        foo.advance_to(0);
        for (x, y) in &[(1, 2), (3, 4), (5, 2), (6, 7)] {
            foo.insert([Variable::new(*x), Variable::new(*y)].into());
        }

        foo.flush();
        foo.advance_to(1);

        for (y, z) in &[(2, 10), (7, 11)] {
            bar.insert([Variable::new(*y), Variable::new(*z)].into());
        }

        bar.flush();
        bar.advance_to(1);
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        [(1, 2, 10), (5, 2, 10), (6, 7, 11)]
            .iter()
            .cloned()
            .map(|(x, y, z)| [Variable::new(x), Variable::new(y), Variable::new(z)].into())
            .collect()
    );
}

#[test]
fn test_antijoin_happy_path() {
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let p1 = Plan::filter(
        Source::new("foo", 2),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let p2 = Plan::filter(Source::new("bar", 1), &[Element::Reference(x.clone())]).expect("ok");
    let antijoin = Plan::antijoin(p1, &[x.clone()], vec![p2]).expect("ok");

    let sink = CaptureSink::new(antijoin.result().into());
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();
        let mut bar = InputSession::new();

        let sources = vec![
            (
                "foo".into(),
                FactCollection::new(2, foo.to_collection(scope)),
            ),
            (
                "bar".into(),
                FactCollection::new(1, bar.to_collection(scope)),
            ),
        ]
        .into_iter()
        .collect::<std::collections::HashMap<String, _>>();

        let captures =
            lower_matching_plan(scope, &mut default_injector, &antijoin, &sources).expect("ok");
        writer.attach(&captures).expect("ok");

        foo.advance_to(0);
        for (x, y) in &[(1, 2), (3, 4), (5, 2), (6, 7)] {
            foo.insert([Variable::new(*x), Variable::new(*y)].into());
        }

        foo.flush();
        foo.advance_to(1);

        for x in &[1, 5] {
            bar.insert([Variable::new(*x)].into());
        }

        bar.flush();
        bar.advance_to(1);
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        [(3, 4), (6, 7)]
            .iter()
            .cloned()
            .map(|(x, y)| [Variable::new(x), Variable::new(y)].into())
            .collect()
    );
}

#[test]
fn test_antijoin_subtrahend_wrong_shape() {
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::plan::Source;
    use crate::unification::Element;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let p1 = Plan::filter(
        Source::new("foo", 2),
        &[Element::Reference(x.clone()), Element::Reference(y.clone())],
    )
    .expect("ok");
    let p2 = Plan::filter(Source::new("bar", 1), &[Element::Reference(x.clone())]).expect("ok");
    let antijoin = Plan::antijoin(p1, &[x.clone()], vec![p2]).expect("ok");

    let sink = CaptureSink::new(antijoin.result().into());
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut foo = InputSession::new();
        let mut bar = InputSession::new();

        let sources = vec![
            (
                "foo".into(),
                FactCollection::new(2, foo.to_collection(scope)),
            ),
            (
                "bar".into(),
                FactCollection::new(1, bar.to_collection(scope)),
            ),
        ]
        .into_iter()
        .collect::<std::collections::HashMap<String, _>>();

        let captures =
            lower_matching_plan(scope, &mut default_injector, &antijoin, &sources).expect("ok");
        writer.attach(&captures).expect("ok");

        foo.advance_to(0);
        for (x, y) in &[(1, 2), (3, 4), (5, 2), (6, 7)] {
            foo.insert([Variable::new(*x), Variable::new(*y)].into());
        }

        foo.flush();
        foo.advance_to(1);

        for x in &[1, 5] {
            bar.insert([Variable::new(*x)].into());
        }

        bar.flush();
        bar.advance_to(1);
    });

    assert_eq!(
        sink.values::<HashSet<_>>(),
        [(3, 4), (6, 7)]
            .iter()
            .cloned()
            .map(|(x, y)| [Variable::new(x), Variable::new(y)].into())
            .collect()
    );
}

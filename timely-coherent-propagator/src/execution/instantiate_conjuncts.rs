//! Coherent Logic includes Datalog as a subset.  These simple rules
//! tend to represent administrative steps in proofs (e.g., complete
//! the transitive closure of an equality relation), and are not
//! usually interesting from a proof search point of view.
//!
//! This module applies Captures as a substitution in Templates, a
//! transformation we need in order to generate derived facts in a
//! naïve bottom-up datalog evaluator.
use super::CaptureCollection;
use super::FactCollection;
use super::FactSink;
use super::FactWriter;
use crate::matching::PredicateFormula;
use crate::unification::Template;
use std::collections::HashMap;
use timely::dataflow::Scope;

/// Derives all the patterns in `derived` from the captures in
/// `input`, and appends the results to the vector corresponding to
/// each derived fact's predicate in `acc`.
///
/// # Errors
///
/// Returns `Err` when some `MetaVar` in the `derived` formula is
/// missing from the `input`'s shape.
pub fn push_conjunct_instances<'a, G, I, H>(
    input: &CaptureCollection<G>,
    derived: I,
    mut acc: HashMap<String, Vec<FactCollection<G>>, H>,
) -> Result<HashMap<String, Vec<FactCollection<G>>, H>, &'static str>
where
    G: Scope,
    I: IntoIterator<Item = &'a PredicateFormula>,
    H: std::hash::BuildHasher,
{
    for formula in derived {
        let facts = instantiate_formula(input, formula)?;

        acc.entry(formula.predicate.clone())
            .or_insert_with(Vec::new)
            .push(facts);
    }

    Ok(acc)
}

/// Accepts a map from predicate name to Fact collections, and
/// attaches each collection to a sink for that predicate.
///
/// # Errors
///
/// Returns `Err` on shape mismatch between a collection and its sink,
/// or between collecions for the same predicate.
pub fn reify_conjunct_instances<
    G: Scope,
    H1: std::hash::BuildHasher,
    H2: std::hash::BuildHasher,
>(
    instances: &HashMap<String, Vec<FactCollection<G>>, H1>,
    mut acc: HashMap<String, FactSink, H2>,
) -> Result<HashMap<String, FactSink, H2>, &'static str> {
    for (name, collections) in instances.iter() {
        let mut writer: Option<FactWriter> = None;

        for collection in collections {
            let dst = writer.get_or_insert_with(|| {
                acc.entry(name.into())
                    .or_insert_with(|| FactSink::new(collection.shape))
                    .writer()
            });

            dst.attach(collection)?;
        }
    }

    Ok(acc)
}

/// Converts each capture in `inputs` to a fact matching `derived`.
fn instantiate_formula<G: Scope>(
    input: &CaptureCollection<G>,
    derived: &PredicateFormula,
) -> Result<FactCollection<G>, &'static str> {
    let template = Template::new(&input.shape, &derived.pattern)?;
    let result_shape = template.output_len();
    let facts = input.container.map(move |capture| template.apply(&capture));

    Ok(FactCollection::new(result_shape, facts))
}

#[test]
fn test_instantiate_formula_happy_path() {
    use super::FactSink;
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let formula = PredicateFormula::new(
        "test",
        [
            Element::Reference(x.clone()),
            Element::Reference(y.clone()),
            Element::Reference(x.clone()),
        ]
        .iter()
        .cloned(),
    );

    let sink = FactSink::new(3);
    let writer = sink.writer();

    timely::execute::example(move |scope| {
        let mut dummy = InputSession::new();

        let captures =
            CaptureCollection::new([x.clone(), y.clone()].into(), dummy.to_collection(scope));
        let derived = instantiate_formula(&captures, &formula).expect("ok");

        writer.attach(&derived).expect("ok");

        dummy.advance_to(0);
        dummy.insert([Variable::new(1), Variable::new(2)].into());
        dummy.insert([Variable::new(2), Variable::new(1)].into());
        dummy.insert([Variable::new(10), Variable::new(11)].into());
        dummy.flush();
        dummy.advance_to(1);
    });

    let expected: HashSet<Fact> = [&[1, 2, 1], &[2, 1, 2], &[10, 11, 10]]
        .iter()
        .map(|ids| {
            ids.iter()
                .map(|i| Variable::new(*i))
                .collect::<Vec<_>>()
                .into()
        })
        .collect();

    assert_eq!(sink.values::<HashSet<_>>(), expected);
}

#[test]
fn test_push_conjuncts_happy_path() {
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashMap;
    use std::collections::HashSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let f1 = PredicateFormula::new(
        "test1",
        [Element::Reference(x.clone()), Element::Reference(y.clone())]
            .iter()
            .cloned(),
    );

    let f2 = PredicateFormula::new(
        "test1",
        [Element::Reference(x.clone()), Element::Reference(x.clone())]
            .iter()
            .cloned(),
    );

    let f3 = PredicateFormula::new(
        "test2",
        [Element::Reference(y.clone()), Element::Reference(x.clone())]
            .iter()
            .cloned(),
    );

    let conjuncts = [f1, f2, f3];
    let sinks: HashMap<String, FactSink> = timely::execute::example(move |scope| {
        let mut dummy = InputSession::new();

        let captures =
            CaptureCollection::new([x.clone(), y.clone()].into(), dummy.to_collection(scope));

        let instance_map =
            push_conjunct_instances(&captures, &conjuncts, HashMap::new()).expect("ok");

        dummy.insert([Variable::new(1), Variable::new(2)].into());
        dummy.insert([Variable::new(10), Variable::new(10)].into());

        reify_conjunct_instances(&instance_map, HashMap::new()).expect("ok")
    });

    let values: HashMap<String, HashSet<Fact>> = sinks
        .iter()
        .map(|(name, sink)| (name.clone(), sink.values()))
        .collect();

    assert_eq!(
        values,
        [
            (
                "test1".into(),
                [
                    [Variable::new(1), Variable::new(2)].into(),
                    [Variable::new(10), Variable::new(10)].into(),
                    [Variable::new(1), Variable::new(1)].into(),
                    [Variable::new(10), Variable::new(10)].into()
                ]
                .iter()
                .cloned()
                .collect()
            ),
            (
                "test2".into(),
                [
                    [Variable::new(2), Variable::new(1)].into(),
                    [Variable::new(10), Variable::new(10)].into(),
                ]
                .iter()
                .cloned()
                .collect()
            )
        ]
        .iter()
        .cloned()
        .collect()
    );
}

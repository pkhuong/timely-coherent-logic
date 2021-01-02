//! The datalog subset of coherent logic only includes trivial
//! sequents where consequents do not include disjunctions (no
//! choice), nor any existential (no variable to instantiate).  We can
//! always derive all trivialities from an initial set of facts,
//! without risking non-termination.
//!
//! This module implements that saturation phase, which should happen
//! before trying to match non-trivial sequents.
use super::lower_matching_plan;
use super::push_conjunct_instances;
use super::FactCollection;
use super::FactVariable;
use crate::ground::Capture;
use crate::matching::plan::Source;
use crate::matching::plan_constraint;
use crate::matching::Constraint;
use crate::matching::PredicateFormula;
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::{collection::concatenate, Collection};
use std::collections::BTreeSet;
use std::collections::HashMap;
use timely::dataflow::scopes::child::Child;
use timely::dataflow::Scope;
use timely::dataflow::ScopeParent;
use timely::order::PartialOrder;
use timely::progress::timestamp::Refines;

/// A trivial sequent represents a rule of the form
/// antecendent_1 /\ antecendent_2 /\ ... => formula_1 /\ formula_2 /\...,
/// where all the metavariables in the right-hand side formulae
/// are matched in the antecendents.
pub struct TrivialSequent {
    antecedents: Constraint,
    consequent: Vec<PredicateFormula>,
}

impl TrivialSequent {
    pub fn new(
        antecedents: Constraint,
        consequent: &[PredicateFormula],
    ) -> Result<TrivialSequent, &'static str> {
        for formula in consequent.iter() {
            let dependencies = formula.insert_metavars(BTreeSet::new());
            if !dependencies.is_subset(antecedents.captures()) {
                return Err("Consequence metavariable not captured in antecedents");
            }
        }

        Ok(TrivialSequent {
            antecedents,
            consequent: consequent.into(),
        })
    }
}

/// Given an initial set of facts `inputs` and a list of trivial
/// sequents, repeatedly applies the sequents to generate new (unique)
/// facts until a fixpoint is reached.
///
/// Returns the unique union of the input facts and all the facts
/// derived from the trivial sequents.
///
/// The `injector` must be a callable that accepts `scope` and vector
/// of values, and returns a collection for `scope` initialised with
/// these values.  This injector will be called with very few distinct
/// vectors; memoisation or caching is probably a good idea.
pub fn saturate_trivialities<G: Input, Injector>(
    scope: &mut G,
    injector: &mut Injector,
    trivia: &[TrivialSequent],
    inputs: &HashMap<String, FactCollection<G>>,
) -> Result<HashMap<String, FactCollection<G>>, &'static str>
where
    G::Timestamp: Lattice + Ord,
    Injector: FnMut(&mut G, Vec<Capture>) -> Collection<G, Capture>,
{
    use timely::order::Product;

    scope.iterative::<usize, _, _>(move |mut child| {
        // We want the inner iteration to advance only the child
        // (innermost) scope.
        let step = Product::new(Default::default(), 1);
        let (planning_sources, cyclic_vars) = setup_sources(child, step, trivia, inputs)?;

        let consequents = gather_consequents(
            &mut child,
            |child, captures| injector(&mut child.parent, captures).enter(&child),
            trivia,
            &planning_sources,
            &cyclic_vars,
        )?;

        squash_results(&mut child, inputs.clone(), cyclic_vars, consequents)
    })
}

type FactMap<G> = HashMap<String, FactCollection<G>>;
type VarMap<'a, G, T> = HashMap<String, FactVariable<Child<'a, G, T>>>;
type InitialSources<'a, G, T> = (HashMap<String, Source>, VarMap<'a, G, T>);

/// Creates initial sources for the union of everything in the inputs,
/// and everything produced by the trivial sequents.
///
/// These initial sources are (cyclic) Variables.  When there is an
/// input, we use that as the initial contents, otherwise, the
/// variable is initialised as empty.  Calling `squash_result` once
/// the outputs are setup will hook any derived fact back up to the
/// variables.
fn setup_sources<'a, G, T>(
    scope: &mut Child<'a, G, T>,
    step: T::Summary,
    trivia: &[TrivialSequent],
    inputs: &FactMap<G>,
) -> Result<InitialSources<'a, G, T>, &'static str>
where
    G: Scope + ScopeParent,
    T: Refines<<G as ScopeParent>::Timestamp> + Lattice,
    G::Timestamp: Lattice,
{
    let mut planning_sources: HashMap<String, Source> = HashMap::new();
    let mut cyclic_vars: HashMap<String, FactVariable<_>> = HashMap::new();

    for (name, split) in inputs.iter() {
        planning_sources.insert(name.clone(), Source::new(name, split.shape));
        cyclic_vars.insert(
            name.clone(),
            FactVariable::new(
                split.shape,
                Variable::new_from(split.container.enter(scope), step.clone()),
            ),
        );
    }

    for sequent in trivia.iter() {
        for formula in sequent.consequent.iter() {
            let name = &formula.predicate;
            let arity = formula.pattern.len();

            if planning_sources
                .entry(name.clone())
                .or_insert_with(|| Source::new(name, arity))
                .arity
                != arity
            {
                return Err("Output arity does not match input.");
            }

            if cyclic_vars
                .entry(name.clone())
                .or_insert_with(|| FactVariable::new(arity, Variable::new(scope, step.clone())))
                .shape
                != arity
            {
                // Covered by the error above.
                #[cfg(not(tarpaulin_include))]
                return Err("Output arity does not match other input.");
            }
        }
    }

    Ok((planning_sources, cyclic_vars))
}

type DerivedMap<'a, G, T> = HashMap<String, Vec<FactCollection<Child<'a, G, T>>>>;

/// Creates a matching and instantiation dataflow graph for each
/// trivial sequent, and returns all the resulting output collections
/// (one for each output predicate in a sequent).
fn gather_consequents<'a, G, T, Injector>(
    child: &mut Child<'a, G, T>,
    mut injector: Injector,
    trivia: &[TrivialSequent],
    planning_sources: &HashMap<String, Source>,
    cyclic_vars: &VarMap<'a, G, T>,
) -> Result<DerivedMap<'a, G, T>, &'static str>
where
    G: Scope + ScopeParent,
    T: Refines<<G as ScopeParent>::Timestamp> + Lattice + PartialOrder,
    Injector: FnMut(&mut Child<'a, G, T>, Vec<Capture>) -> Collection<Child<'a, G, T>, Capture>,
{
    let mut consequents: HashMap<String, Vec<FactCollection<_>>> = HashMap::new();

    // These collections refer to the result of joining the
    // initial input values with the anything written in there,
    // after removing duplicates.
    let joined_inputs: HashMap<String, FactCollection<_>> = cyclic_vars
        .iter()
        .map(|(key, var)| {
            (
                key.clone(),
                // Don't `distinct()` here: we already do so on before
                // hooking an output up to cyclic variables.
                FactCollection::new(var.shape, var.container.clone()),
            )
        })
        .collect();

    for sequent in trivia.iter() {
        let plan = plan_constraint(&sequent.antecedents, &planning_sources)?;
        let captures = lower_matching_plan(child, &mut injector, &plan, &joined_inputs)?;
        consequents = push_conjunct_instances(&captures, &sequent.consequent, consequents)?;
    }

    Ok(consequents)
}

/// Closes the loop for every value in `cyclic_var`.  If there is an
/// initial collecion in `inputs`, it must be kept.  If there are also
/// results in `consequents`, the must be added to the variable.
fn squash_results<'a, G: Input, T>(
    child: &mut Child<'a, G, T>,
    mut inputs: HashMap<String, FactCollection<G>>,
    cyclic_vars: HashMap<String, FactVariable<Child<'a, G, T>>>,
    mut consequents: HashMap<String, Vec<FactCollection<Child<'a, G, T>>>>,
) -> Result<HashMap<String, FactCollection<G>>, &'static str>
where
    T: Refines<<G as ScopeParent>::Timestamp> + Lattice,
{
    use crate::ground::Fact;
    use differential_dataflow::operators::reduce::Threshold;

    let mut result = HashMap::new();
    for (pred, fvar) in cyclic_vars.into_iter() {
        let shape = fvar.shape;
        let mut to_merge = Vec::<Collection<Child<'a, G, T>, Fact>>::new();

        for inp in inputs.remove(&pred).iter() {
            if inp.shape != shape {
                // We check for this in `setup_sources`.
                #[cfg(not(tarpaulin_include))]
                return Err("Input shape differs from variable shape.");
            }

            to_merge.push(inp.container.enter(child));
        }

        for out in consequents.remove(&pred).unwrap_or_default().into_iter() {
            if out.shape != shape {
                // We check for this in `setup_sources`.
                #[cfg(not(tarpaulin_include))]
                return Err("Output shape differs from variable shape");
            }

            to_merge.push(out.container);
        }

        let merged = concatenate(child, to_merge.into_iter()).distinct();
        fvar.container.set(&merged);
        result.insert(pred, FactCollection::new(shape, merged.leave()));
    }

    Ok(result)
}

#[test]
fn test_trivial_sequent_happy_path() {
    use crate::unification::Element;
    use crate::unification::MetaVar;

    // Construct a transitive reachability predicate:
    //   dr(x, y) /\ dr(y, z) -> dr(x, z)
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "dr",
                &[Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");
    let rhs = PredicateFormula::new(
        "dr",
        &[Element::Reference(x.clone()), Element::Reference(z.clone())],
    );

    TrivialSequent::new(lhs, &[rhs]).expect("must build correctly");
}

#[test]
fn test_trivial_sequent_detect_missing_capture() {
    use crate::unification::Element;
    use crate::unification::MetaVar;

    // Construct a transitive reachability predicate:
    //   dr(x, y) /\ dr(y, z) -> dr(x, z),
    // but forget to capture z.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "dr",
                &[Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");
    let rhs = PredicateFormula::new(
        "dr2",
        &[Element::Reference(x.clone()), Element::Reference(z.clone())],
    );

    assert!(TrivialSequent::new(lhs, &[rhs]).is_err());
}

#[test]
fn test_trivial_happy_path() {
    use super::sink_all_collections;
    use super::FactSink;
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Compute the transitive closure of a directed reachability
    // relation dr(a, b).
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "dr",
                &[Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");
    let rhs = PredicateFormula::new(
        "dr",
        &[Element::Reference(x.clone()), Element::Reference(z.clone())],
    );

    let sequent = TrivialSequent::new(lhs, &[rhs]).expect("ok");

    let sinks: HashMap<String, FactSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "dr".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        let saturated = saturate_trivialities(
            scope,
            &mut |scope, values| scope.new_collection_from(values).1,
            &[sequent],
            &initial_inputs,
        )
        .expect("ok");

        let ret = sink_all_collections(saturated.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        initial.insert([Variable::new(2), Variable::new(3)].into());
        initial.insert([Variable::new(3), Variable::new(4)].into());
        initial.insert([Variable::new(4), Variable::new(6)].into());
        initial.insert([Variable::new(5), Variable::new(4)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    // There should only be one output sink, "dr".
    let expected_keys = ["dr".into()].iter().cloned().collect::<HashSet<_>>();
    assert_eq!(
        sinks.keys().cloned().collect::<HashSet<String>>(),
        expected_keys
    );

    let expected_facts = [
        // We initially have
        //   dr(2, 3)
        //   dr(3, 4)
        //   dr(4, 6)
        //   dr(5, 4)
        [2, 3],
        [3, 4],
        [4, 6],
        [5, 4],
        // From that, we can derive
        //   dr(2, 4)
        //   dr(3, 6)
        //   dr(5, 4)
        [2, 4],
        [5, 6],
        [3, 6],
        // And finally,
        //   dr(2, 6)
        [2, 6],
    ]
    .iter()
    .map(|ids| Fact::from_vec(ids.iter().map(|i| Variable::new(*i)).collect()))
    .collect();
    assert_eq!(
        sinks.get("dr").expect("has_value").values::<HashSet<_>>(),
        expected_facts
    );
}

#[test]
fn test_trivial_two_sequents() {
    use super::sink_all_collections;
    use super::FactSink;
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Compute the transitive closure of an *undirected* reachability
    // relation dr(a, b).
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let transitivity = {
        let lhs = Constraint::new(
            [x.clone(), z.clone()].iter().cloned().collect(),
            vec![
                PredicateFormula::new(
                    "dr",
                    &[Element::Reference(x.clone()), Element::Reference(y.clone())],
                ),
                PredicateFormula::new(
                    "dr",
                    &[Element::Reference(y.clone()), Element::Reference(z.clone())],
                ),
            ],
        )
        .expect("ok");
        let rhs = PredicateFormula::new(
            "dr",
            &[Element::Reference(x.clone()), Element::Reference(z.clone())],
        );

        TrivialSequent::new(lhs, &[rhs]).expect("ok")
    };

    let commutativity = {
        let lhs = Constraint::new(
            [x.clone(), y.clone()].iter().cloned().collect(),
            vec![PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            )],
        )
        .expect("ok");
        let rhs = PredicateFormula::new(
            "dr",
            &[Element::Reference(y.clone()), Element::Reference(x.clone())],
        );

        TrivialSequent::new(lhs, &[rhs]).expect("ok")
    };

    let sinks: HashMap<String, FactSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "dr".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        let saturated = saturate_trivialities(
            scope,
            &mut |scope, values| scope.new_collection_from(values).1,
            &[transitivity, commutativity],
            &initial_inputs,
        )
        .expect("ok");

        let ret = sink_all_collections(saturated.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        initial.insert([Variable::new(2), Variable::new(3)].into());
        initial.insert([Variable::new(3), Variable::new(4)].into());
        initial.insert([Variable::new(5), Variable::new(6)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    // There should only be one output sink, "dr".
    let expected_keys = ["dr".into()].iter().cloned().collect::<HashSet<_>>();
    assert_eq!(
        sinks.keys().cloned().collect::<HashSet<String>>(),
        expected_keys
    );

    let expected_facts = [
        // We initially have
        //   dr(2, 3)
        //   dr(3, 4)
        //   dr(5, 6)
        [2, 3],
        [3, 4],
        [5, 6],
        // From that, we can derive that {2, 3, 4} is connected in
        // both direcions.
        [2, 4],
        // And flip the arcs in {2, 3, 4}.
        [3, 2],
        [4, 3],
        [4, 2],
        // And we can also flip dr(5, 6) -> dr(6, 5)
        [6, 5],
        // And make it reflexive: dr(x, y) -> dr(y, x), and
        //  dr(x, y) /\ dr(y, x) -> dr(x, x) /\ dr(y, y)
        [2, 2],
        [3, 3],
        [4, 4],
        [5, 5],
        [6, 6],
    ]
    .iter()
    .map(|ids| Fact::from_vec(ids.iter().map(|i| Variable::new(*i)).collect()))
    .collect();
    assert_eq!(
        sinks.get("dr").expect("has_value").values::<HashSet<_>>(),
        expected_facts
    );
}

#[test]
fn test_trivial_write_to_new_dst() {
    use super::sink_all_collections;
    use super::FactSink;
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Set up the same sequent, but don't close the loop, and let the
    // newly discovered arcs go to "dr2".
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "dr",
                &[Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");
    let rhs = PredicateFormula::new(
        "dr2",
        &[Element::Reference(x.clone()), Element::Reference(z.clone())],
    );

    let sequent = TrivialSequent::new(lhs, &[rhs]).expect("ok");

    let sinks: HashMap<String, FactSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "dr".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        let saturated = saturate_trivialities(
            scope,
            &mut |scope, values| scope.new_collection_from(values).1,
            &[sequent],
            &initial_inputs,
        )
        .expect("ok");

        let ret = sink_all_collections(saturated.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        initial.insert([Variable::new(2), Variable::new(3)].into());
        initial.insert([Variable::new(3), Variable::new(4)].into());
        initial.insert([Variable::new(5), Variable::new(4)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    // We should have "dr", the initial relation, and "dr2", the new
    // (output) relation.
    let expected_keys = ["dr".into(), "dr2".into()]
        .iter()
        .cloned()
        .collect::<HashSet<_>>();
    assert_eq!(
        sinks.keys().cloned().collect::<HashSet<String>>(),
        expected_keys
    );

    // Initial facts haven't changed.
    let initial_facts = [[2, 3], [3, 4], [5, 4]]
        .iter()
        .map(|ids| Fact::from_vec(ids.iter().map(|i| Variable::new(*i)).collect()))
        .collect();
    assert_eq!(
        sinks.get("dr").expect("has_value").values::<HashSet<_>>(),
        initial_facts
    );

    // We should derive dr2(2, 4)
    let derived_facts = [[Variable::new(2), Variable::new(4)].into()]
        .iter()
        .cloned()
        .collect();
    assert_eq!(
        sinks.get("dr2").expect("has_value").values::<HashSet<_>>(),
        derived_facts
    );
}

#[test]
// TODO: figure out if timely could handle this better.  We detect the
// mismatch correctly, but, because we don't `set` every cyclic
// variable before exiting with error, we hit an assertion failure in
// timely/src/progress/subgraph.rs.
#[should_panic(
    expected = "assertion failed: self.children.iter().enumerate().all(|(i, x)| i == x.index)"
)]
fn test_trivial_incorrect_arity() {
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;

    // See what happens when we try to write 3-variable facts in a
    // 2-variable predicate.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), y.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "dr",
                &[Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");
    let rhs = PredicateFormula::new(
        "dr",
        &[
            Element::Reference(x.clone()),
            Element::Reference(y.clone()),
            Element::Reference(z.clone()),
        ],
    );

    let sequent = TrivialSequent::new(lhs, &[rhs]).expect("ok");

    let result = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "dr".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        saturate_trivialities(
            scope,
            &mut |scope, values| scope.new_collection_from(values).1,
            &[sequent],
            &initial_inputs,
        )
        .map(|_| ())
    });

    assert!(result.is_err());
}

#[test]
// TODO: figure out if timely could handle this better.
#[should_panic(
    expected = "assertion failed: self.children.iter().enumerate().all(|(i, x)| i == x.index)"
)]
fn test_trivial_incorrect_arity_output_only() {
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;

    // See what happens when we try to write 3-variable and 2-variable
    // facts in the same output predicate.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), y.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "dr",
                &[Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "dr",
                &[Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");
    let rhses = [
        PredicateFormula::new(
            "dr2",
            &[
                Element::Reference(x.clone()),
                Element::Reference(y.clone()),
                Element::Reference(z.clone()),
            ],
        ),
        PredicateFormula::new(
            "dr2",
            &[Element::Reference(x.clone()), Element::Reference(z.clone())],
        ),
    ];

    let sequent = TrivialSequent::new(lhs, &rhses).expect("ok");

    let result = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "dr".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        saturate_trivialities(
            scope,
            &mut |scope, values| scope.new_collection_from(values).1,
            &[sequent],
            &initial_inputs,
        )
        .map(|_| ())
    });

    assert!(result.is_err());
}

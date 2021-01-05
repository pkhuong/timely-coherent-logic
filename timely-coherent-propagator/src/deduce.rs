//! Deduction is the core of our coherent logic prover:
//! `deduction_graph_from_sequents` turns a set of axioms into a
//! differential dataflow graph that accepts a set of facts, and
//! outputs all the facts that could be derived from that initial
//! information, as well as sequents that could be instantiated from
//! the initial information and all derived facts.
//!
//! The computation automatically responds to changes in the input
//! facts.  The first return value of `deduction_graph_from_sequents`
//! is a `HashMap` from predicate name to `FactInput`; one can insert
//! (or remove) facts into any of these `InputSession`s,
//! `advance_all_fact_inputs` to make sure the changes are visible and
//! time has advanced, and the changes' impact on the output
//! `DeductionSink`s will eventually be visible.
//!
//! After one has called `advance_all_fact_inputs` with a fresly
//! increased `timestamp`, calling `worker.step_while(||
//! sinks.probe.less_than(&timestamp));` will update the dataflow
//! graph until it has caught up to the facts written before
//! `advance_all_fact_inputs`.
use crate::execution::enumerate_instantiation_candidates;
use crate::execution::saturate_trivialities;
use crate::execution::sink_all_collections;
use crate::execution::CaptureCollection;
use crate::execution::CaptureSink;
use crate::execution::FactCollection;
use crate::execution::FactInput;
use crate::execution::FactSink;
use crate::execution::SearchSequent;
use crate::execution::TrivialSequent;
use crate::matching::Constraint;
use crate::matching::PredicateFormula;
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use std::collections::HashMap;
use timely::dataflow::operators::probe::Handle;
use timely::dataflow::Scope;
use timely::progress::Timestamp;

/// `DeductionSink`s are `FactSink`s keyed on predicates, and
/// `CaptureSink`s keyed on sequents.
///
/// The `probe` summarises the progress status of all collections
/// underlying Fact and Capture sinks.
#[derive(Clone)]
pub struct DeductionSink<T: Timestamp> {
    pub probe: Handle<T>,
    pub facts: HashMap<String, FactSink>,
    pub instances: HashMap<SearchSequent, CaptureSink>,
}

/// Accepts a scope and vectors of trivial and search sequents, and
/// returns a `HashMap` of `FactInput`s, as well a `DeductionSink`.
///
/// The inputs are hooked up to the dataflow graph for deductions from
/// the trivial and search sequents, and eventually affect the results
/// reported in the `DeductionSink`.
///
/// # Errors
///
/// Returns `Err` on shape mismatches, e.g., when the same predicate
/// appears with different arities in sequents.
pub fn deduction_graph_from_sequents<G, T>(
    scope: &mut G,
    trivia: Vec<TrivialSequent>,
    sequents: Vec<SearchSequent>,
) -> Result<(HashMap<String, FactInput<T>>, DeductionSink<T>), &'static str>
where
    G: Input<Timestamp = T>,
    T: Timestamp + Lattice + Ord,
{
    let predicate_shapes = sequents_predicate_shapes(&trivia, &sequents)?;
    let sources = DeductionSource::new(scope, &predicate_shapes)?;
    let results = deduce_from_sequents(scope, &sources.collections, trivia, sequents)?;

    Ok((sources.inputs, results.into_sinks()))
}

/// Advances all `FactInput`s in `iterator` to `ts`, and guarantees
/// the time update is visible.
pub fn advance_all_fact_inputs<'a, I, T>(iterator: I, ts: &T)
where
    I: IntoIterator<Item = &'a mut FactInput<T>>,
    T: Timestamp + Clone,
{
    for input in iterator {
        // All the examples in the DD book are wrong.  The timestamp
        // change isn't guaranteed to be visible until flushed.
        input.container.advance_to(ts.clone());
        input.container.flush();
    }
}

/// `DeductionSource`s are parallel maps from predicate name to
/// tagged `InputSession` and associated `Collection`.
pub struct DeductionSource<G: Scope> {
    pub inputs: HashMap<String, FactInput<G::Timestamp>>,
    pub collections: HashMap<String, FactCollection<G>>,
}

impl<G: Input> DeductionSource<G> {
    /// Constructs a `DeductionSource` from an iterator of predicate
    /// `(name, arity)`.
    ///
    /// # Errors
    ///
    /// Returns `Err` when a predicate name is repeated (even if the
    /// arity matches).
    pub fn new<'a, I>(scope: &mut G, predicates: I) -> Result<DeductionSource<G>, &'static str>
    where
        I: IntoIterator<Item = (&'a String, &'a usize)>,
    {
        let mut inputs = HashMap::new();
        let mut collections = HashMap::new();

        for (name, arity) in predicates {
            let (input, collection) = scope.new_collection();
            if inputs
                .insert(name.clone(), FactInput::new(*arity, input))
                .is_some()
            {
                return Err("Duplicate predicate definition.");
            }

            if collections
                .insert(name.clone(), FactCollection::new(*arity, collection))
                .is_some()
            {
                // This case is covered by the same check above.
                #[cfg(not(tarpaulin_include))]
                return Err("Duplicate predicate definition.");
            }
        }

        Ok(Self {
            inputs,
            collections,
        })
    }
}

/// `DeductionCollection`s consist of collections of facts (one for
/// each predicate), and of captures for sequents to instantiate.
#[derive(Clone)]
pub struct DeductionCollection<G: Scope> {
    pub facts: HashMap<String, FactCollection<G>>,
    pub instances: HashMap<SearchSequent, CaptureCollection<G>>,
}

impl<G: Scope> DeductionCollection<G> {
    /// Converts each `FactCollection` in this `DeductionCollection`
    /// into a `FactSink`, and returns the corresponding
    /// `DeductionSink`.
    #[must_use]
    pub fn into_sinks(self) -> DeductionSink<G::Timestamp> {
        let mut probe = Handle::new();
        for fact in self.facts.values() {
            fact.container.probe_with(&mut probe);
        }

        for instance in self.instances.values() {
            instance.container.probe_with(&mut probe);
        }

        // These calls should never fail because `facts` and
        // `instances` are maps, so keys are unique.
        let facts = sink_all_collections(self.facts, HashMap::new())
            .expect("HashMap guarantees unique predicate specs");
        let instances = sink_all_collections(self.instances, HashMap::new())
            .expect("HashMap guarantees unique predicate specs");

        DeductionSink {
            probe,
            facts,
            instances,
        }
    }
}

/// Given a list of trivial sequents and another of search sequents,
/// returns a map of all known predicates, along with their shapes.
///
/// # Errors
///
/// Returns `Err` when a predicate appears with multiple shapes.
pub fn sequents_predicate_shapes<'a, I, J>(
    trivia: I,
    search: J,
) -> Result<HashMap<String, usize>, &'static str>
where
    I: IntoIterator<Item = &'a TrivialSequent>,
    J: IntoIterator<Item = &'a SearchSequent>,
{
    let mut result: HashMap<String, usize> = HashMap::new();

    let observe_predicate = |acc: &mut HashMap<String, usize>, pred: &PredicateFormula| {
        let arity = pred.pattern.len();
        if arity != *acc.entry(pred.predicate.clone()).or_insert(arity) {
            return Err("Mismatched predicate size");
        }
        Ok(())
    };

    let observe_constraint = |acc: &mut _, constraint: &Constraint| {
        for conjunct in constraint.conjuncts() {
            observe_predicate(acc, conjunct)?;
        }

        Ok(())
    };

    for sequent in trivia {
        observe_constraint(&mut result, sequent.antecedents())?;
        for pred in sequent.consequent() {
            observe_predicate(&mut result, pred)?;
        }
    }

    for sequent in search {
        observe_constraint(&mut result, sequent.antecedents())?;
        for consequent in sequent.consequents() {
            observe_constraint(&mut result, consequent)?;
        }
    }

    Ok(result)
}

/// Returns collections of facts and instances derived from the
/// `trivia`l and search `sequents`, and updated whenever the `inputs`
/// change.
///
/// # Errors
///
/// Returns `Err` on planning issues, primarily when the one of
/// inputs' shape differs from its shape in the sequents.
pub fn deduce_from_sequents<G, H, Trivia, Sequents>(
    scope: &mut G,
    inputs: &HashMap<String, FactCollection<G>, H>,
    trivia: Trivia,
    sequents: Sequents,
) -> Result<DeductionCollection<G>, &'static str>
where
    G: Input,
    G::Timestamp: Lattice + Ord,
    H: std::hash::BuildHasher + Clone,
    Trivia: IntoIterator<Item = TrivialSequent>,
    Sequents: IntoIterator<Item = SearchSequent>,
{
    let facts = saturate_trivialities(scope, trivia, &inputs)?;
    let instances = enumerate_instantiation_candidates(scope, sequents, &facts)?;

    Ok(DeductionCollection {
        facts: facts.into_iter().collect(),
        instances,
    })
}

#[test]
fn test_deduction_sources_happy_path() {
    use std::collections::HashSet;

    // Build sources for "foo" of arity 4 and "bar" of arity 1.
    let predicates: [(String, usize); 2] = [("foo".into(), 4), ("bar".into(), 1)];

    timely::execute::example(move |scope| {
        let sources =
            DeductionSource::new(scope, predicates.iter().map(|(x, y)| (x, y))).expect("ok");

        let expected_keys: HashSet<String> = ["foo".into(), "bar".into()].iter().cloned().collect();

        assert_eq!(
            sources.inputs.keys().cloned().collect::<HashSet<_>>(),
            expected_keys
        );
        assert_eq!(
            sources.collections.keys().cloned().collect::<HashSet<_>>(),
            expected_keys
        );

        assert_eq!(sources.inputs.get("foo").expect("found").shape, 4);
        assert_eq!(sources.inputs.get("bar").expect("found").shape, 1);

        assert_eq!(sources.collections.get("foo").expect("found").shape, 4);
        assert_eq!(sources.collections.get("bar").expect("found").shape, 1);
    });
}

#[test]
fn test_deduction_sources_conflict() {
    // Build sources for "foo" of arity 4 and "bar" of arity 1...  and
    // then try to add another source for "foo" of arity 3.
    // This should fail.
    let predicates: [(String, usize); 3] =
        [("foo".into(), 4), ("bar".into(), 1), ("foo".into(), 3)];

    timely::execute::example(move |scope| {
        assert!(DeductionSource::new(scope, predicates.iter().map(|(x, y)| (x, y))).is_err());
    });
}

#[test]
fn test_sequents_predicate_shapes_happy_path() {
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use std::collections::BTreeSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    // Make sure we collect the shape for predicates in trivial and
    // search sequents.
    let transitivity = {
        let lhs = Constraint::new(
            [x.clone(), z.clone()].iter().cloned().collect(),
            vec![
                PredicateFormula::new(
                    "dr",
                    vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
                ),
                PredicateFormula::new(
                    "dr",
                    vec![Element::Reference(y.clone()), Element::Reference(z.clone())],
                ),
            ],
        )
        .expect("ok");
        let rhs = PredicateFormula::new(
            "dr",
            vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
        );

        TrivialSequent::new(lhs, vec![rhs]).expect("ok")
    };

    // Empty antecedent represents a choice in initial facts.
    let choice = {
        let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

        let rhs1 = Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new(
                "p",
                vec![Element::Reference(x.clone())],
            )],
        )
        .expect("ok");

        let rhs2 = Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new(
                "q",
                vec![
                    Element::Reference(x.clone()),
                    Element::Reference(y.clone()),
                    Element::Reference(z.clone()),
                ],
            )],
        )
        .expect("ok");

        SearchSequent::new(lhs, vec![rhs1, rhs2]).expect("ok")
    };

    let shapes = sequents_predicate_shapes(&[transitivity], &[choice]).expect("ok");

    assert_eq!(
        shapes,
        [("dr".into(), 2), ("p".into(), 1), ("q".into(), 3)]
            .iter()
            .cloned()
            .collect()
    );
}

#[test]
fn test_sequents_predicate_shapes_conflict() {
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use std::collections::BTreeSet;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    // Same test as the happy path, but now one of the "dr" predicate
    // has arity 3 instead of 2.  This should fail.
    let transitivity = {
        let lhs = Constraint::new(
            [x.clone(), z.clone()].iter().cloned().collect(),
            vec![
                PredicateFormula::new(
                    "dr",
                    vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
                ),
                PredicateFormula::new(
                    "dr",
                    vec![Element::Reference(y.clone()), Element::Reference(z.clone())],
                ),
            ],
        )
        .expect("ok");
        let rhs = PredicateFormula::new(
            "dr",
            vec![
                Element::Reference(x.clone()),
                Element::Reference(x.clone()),
                Element::Reference(z.clone()),
            ],
        );

        TrivialSequent::new(lhs, vec![rhs]).expect("ok")
    };

    // Empty antecedent represents a choice in initial facts.
    let choice = {
        let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

        let rhs1 = Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new(
                "p",
                vec![Element::Reference(x.clone())],
            )],
        )
        .expect("ok");

        let rhs2 = Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new(
                "q",
                vec![
                    Element::Reference(x.clone()),
                    Element::Reference(y.clone()),
                    Element::Reference(z.clone()),
                ],
            )],
        )
        .expect("ok");

        SearchSequent::new(lhs, vec![rhs1, rhs2]).expect("ok")
    };

    assert!(sequents_predicate_shapes(&[transitivity], &[choice]).is_err());
}

#[test]
fn test_deduce_all_trivial() {
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use std::collections::BTreeSet;

    // Implement https://github.com/daghovland/clp.test/blob/master/formats/TPTP/anc.in.p
    // fof(initial_model, axiom, dom(berta)  &  dom(ada)  &  dom(cyril)  &  dom(cecilie)  &  dom(david)  &  dom(eve)  &  parent(berta,ada)  &  parent(cyril,berta)  &  parent(cecilie,berta)  &  parent(david,cyril)).
    // fof(goal_ax,axiom, (ancestor(david,ada) =>  goal )).
    // fof(anc_eve,axiom, ![ X] : (dom(X) => ancestor(eve,X) )).
    // fof(par_anc,axiom, ![ X, Y] : (parent(X,Y) => ancestor(X,Y) )).
    // fof(trAns,axiom, ![ X, Y, Z] : ((ancestor(X,Y) & ancestor(Y,Z)) => ancestor(X,Z) )).
    // fof(goal_to_be_proved,conjecture,( goal )).

    // There is no choice or existential in these rules, so just the
    // trivial datalog engine should reach the goal.

    let (x, y, z) = (MetaVar::new("x"), MetaVar::new("y"), MetaVar::new("z"));

    // Lay out the initial model.
    let (ada, berta, cecilie, cyril, david, eve) = (
        Variable::fresh(),
        Variable::fresh(),
        Variable::fresh(),
        Variable::fresh(),
        Variable::fresh(),
        Variable::fresh(),
    );

    let mut initial_model = Vec::new();
    for person in &[ada, berta, cecilie, cyril, david, eve] {
        initial_model.push(PredicateFormula::new(
            "dom",
            vec![Element::Constant(*person)],
        ));
    }

    for (parent, child) in &[
        (berta, ada),
        (cyril, berta),
        (cecilie, berta),
        (david, cyril),
    ] {
        initial_model.push(PredicateFormula::new(
            "parent",
            vec![Element::Constant(*parent), Element::Constant(*child)],
        ));
    }

    let initial_model_sequent = TrivialSequent::new(
        Constraint::new(BTreeSet::new(), vec![]).expect("ok"),
        initial_model,
    )
    .expect("ok");

    // fof(goal_ax,axiom, (ancestor(david,ada) =>  goal )).
    let goal_sequent = TrivialSequent::new(
        Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new(
                "ancestor",
                vec![Element::Constant(david), Element::Constant(ada)],
            )],
        )
        .expect("ok"),
        vec![PredicateFormula::new("goal", vec![])],
    )
    .expect("ok");

    // fof(anc_eve,axiom, ![ X] : (dom(X) => ancestor(eve,X) )).
    let anc_eve_sequent = TrivialSequent::new(
        Constraint::new(
            vec![x.clone()].into_iter().collect(),
            vec![PredicateFormula::new(
                "dom",
                vec![Element::Reference(x.clone())],
            )],
        )
        .expect("ok"),
        vec![PredicateFormula::new(
            "ancestor",
            vec![Element::Constant(eve), Element::Reference(x.clone())],
        )],
    )
    .expect("ok");

    // fof(par_anc,axiom, ![ X, Y] : (parent(X,Y) => ancestor(X,Y) )).
    let par_anc_sequent = TrivialSequent::new(
        Constraint::new(
            vec![x.clone(), y.clone()].into_iter().collect(),
            vec![PredicateFormula::new(
                "parent",
                vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
            )],
        )
        .expect("ok"),
        vec![PredicateFormula::new(
            "ancestor",
            vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
        )],
    )
    .expect("ok");

    // fof(trAns,axiom, ![ X, Y, Z] : ((ancestor(X,Y) & ancestor(Y,Z)) => ancestor(X,Z) )).
    let trans_sequent = TrivialSequent::new(
        Constraint::new(
            vec![x.clone(), y.clone(), z.clone()].into_iter().collect(),
            vec![
                PredicateFormula::new(
                    "ancestor",
                    vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
                ),
                PredicateFormula::new(
                    "ancestor",
                    vec![Element::Reference(y.clone()), Element::Reference(z.clone())],
                ),
            ],
        )
        .expect("ok"),
        vec![PredicateFormula::new(
            "ancestor",
            vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
        )],
    )
    .expect("ok");

    let trivia = vec![
        initial_model_sequent,
        goal_sequent,
        anc_eve_sequent,
        par_anc_sequent,
        trans_sequent,
    ];
    let sequents = Vec::new();

    timely::execute_directly(move |worker| {
        let sinks = worker.dataflow(move |scope| {
            let predicate_shapes = sequents_predicate_shapes(&trivia, &sequents).expect("ok");
            let sources = DeductionSource::new(scope, &predicate_shapes).expect("ok");
            let results =
                deduce_from_sequents(scope, &sources.collections, trivia, sequents).expect("ok");
            results.into_sinks()
        });

        worker.step_while(|| sinks.probe.less_than(&1));
        assert_eq!(
            sinks.facts.get("goal").expect("ok").values::<Vec<_>>(),
            vec![Fact::from_slice(&[])]
        );
    });
}

#[test]
fn test_deduce_straight_through() {
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use std::collections::BTreeSet;
    use std::collections::HashSet;

    let p = Variable::fresh();

    // See what happens to facts we write in, when there's only a
    // dummy rule.
    let assump = {
        let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

        let rhs = Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new("t", vec![Element::Constant(p)])],
        )
        .expect("ok");

        SearchSequent::new(lhs, vec![rhs]).expect("ok")
    };

    timely::execute_directly(move |worker| {
        let sequents = vec![assump.clone()];

        let (mut sources, sinks) = worker.dataflow(move |scope| {
            let predicate_shapes = sequents_predicate_shapes(&[], &sequents).expect("ok");
            let sources = DeductionSource::new(scope, &predicate_shapes).expect("ok");

            let results =
                deduce_from_sequents(scope, &sources.collections, vec![], sequents).expect("ok");

            (sources.inputs, results.into_sinks())
        });

        advance_all_fact_inputs(sources.values_mut(), &1);
        worker.step_while(|| sinks.probe.less_than(&1));

        // Ok, now add some facts to the "t" source.
        let dst = sources.get_mut("t").expect("found");
        for i in 1..10 {
            assert_eq!(dst.shape, 1);
            dst.container.insert(Fact::from_slice(&[Variable::new(i)]));
        }

        // with the new "t"rue facts, we should be able to deduce the
        // goal.
        advance_all_fact_inputs(sources.values_mut(), &2);
        worker.step_while(|| sinks.probe.less_than(&2));

        assert_eq!(
            sinks.facts.get("t").expect("found").values::<HashSet<_>>(),
            (1..10)
                .map(|i| Fact::from_slice(&[Variable::new(i)]))
                .collect::<HashSet<_>>()
        );
    });
}

#[test]
fn test_deduce() {
    use crate::ground::Capture;
    use crate::ground::Fact;
    use crate::ground::Variable;
    use crate::unification::Element;
    use std::collections::BTreeSet;
    use std::collections::HashSet;

    // Implement https://github.com/daghovland/clp.test/blob/master/formats/TPTP/and3or.in.p
    // fof(assump,axiom, ( $true  => (((p & q & r))|((q & r & p))|((r & p & q))) )).
    // fof(goal_ax,axiom, ((r & q & p) =>  goal )).
    // fof(goal_to_be_proved,conjecture,( goal )).

    let (p, q, r) = (Variable::fresh(), Variable::fresh(), Variable::fresh());

    // fof(assump,axiom, ( $true  => (((p & q & r))|((q & r & p))|((r & p & q))) )).
    let assump = {
        let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

        let rhs1 = Constraint::new(
            BTreeSet::new(),
            [p, q, r]
                .iter()
                .map(|v| PredicateFormula::new("t", vec![Element::Constant(*v)]))
                .collect::<Vec<_>>(),
        )
        .expect("ok");

        let rhs2 = Constraint::new(
            BTreeSet::new(),
            [q, r, p]
                .iter()
                .map(|v| PredicateFormula::new("t", vec![Element::Constant(*v)]))
                .collect::<Vec<_>>(),
        )
        .expect("ok");

        let rhs3 = Constraint::new(
            BTreeSet::new(),
            [r, p, q]
                .iter()
                .map(|v| PredicateFormula::new("t", vec![Element::Constant(*v)]))
                .collect::<Vec<_>>(),
        )
        .expect("ok");

        SearchSequent::new(lhs, vec![rhs1, rhs2, rhs3]).expect("ok")
    };

    // fof(goal_ax,axiom, ((r & q & p) =>  goal )).
    let goal = TrivialSequent::new(
        Constraint::new(
            BTreeSet::new(),
            [r, q, p]
                .iter()
                .map(|v| PredicateFormula::new("t", vec![Element::Constant(*v)]))
                .collect::<Vec<_>>(),
        )
        .expect("ok"),
        vec![PredicateFormula::new("goal", vec![])],
    )
    .expect("ok");

    timely::execute_directly(move |worker| {
        let trivia = vec![goal.clone()];
        let expected_assump = assump.clone();
        let sequents = vec![assump.clone()];

        let (mut sources, sinks) = worker.dataflow(move |scope| {
            deduction_graph_from_sequents(scope, trivia, sequents).expect("ok")
        });

        advance_all_fact_inputs(sources.values_mut(), &1);
        worker.step_while(|| sinks.probe.less_than(&1));

        {
            let keys: HashSet<String> = vec!["t".into(), "goal".into()].into_iter().collect();
            assert_eq!(
                sinks.facts.keys().cloned().collect::<HashSet<String>>(),
                keys
            );
            // We're not at a goal state yet.
            assert_eq!(
                sinks.facts.get("goal").expect("found").values::<Vec<_>>(),
                vec![]
            );

            assert_eq!(sinks.instances.len(), 1);
            assert_eq!(
                sinks
                    .instances
                    .get(&expected_assump)
                    .expect("found")
                    .values::<Vec<_>>(),
                vec![Capture::from_slice(&[])]
            );
        }

        // Ok, now add some facts to the "t" source.
        let dst = sources.get_mut("t").expect("found");
        for v in &[p, q, r] {
            assert_eq!(dst.shape, 1);
            dst.container.insert(Fact::from_slice(&[*v]));
        }

        // with the new "t"rue facts, we should be able to deduce the
        // goal.
        advance_all_fact_inputs(sources.values_mut(), &2);
        worker.step_while(|| sinks.probe.less_than(&2));

        assert_eq!(
            sinks.facts.get("goal").expect("found").values::<Vec<_>>(),
            vec![Fact::from_slice(&[])]
        );
    });
}

// TODO: find a simple example that really exercises both trivial and
// search sequents.  The might be something in
// https://github.com/janicicpredrag/Larus/tree/master/benchmarks

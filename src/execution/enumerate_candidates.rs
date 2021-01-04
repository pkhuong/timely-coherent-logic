//! The core of a (forward) coherent logic solver is finding captures
//! matching a sequent's antecedents, and for which the none of the
//! corresponding consequents are already known to be true.
//!
//! This module implements that search, by listing all candidate
//! captures, but not instantiate any of them, and especially not
//! decide which of the consequents might be of interest.  We leave
//! these difficult decisions to a higher level module.
use super::default_injector;
use super::lower_matching_plan;
use super::CaptureCollection;
use super::FactCollection;
use crate::matching::plan::Source;
use crate::matching::plan_sequent;
use crate::matching::Constraint;
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use std::collections::BTreeSet;
use std::collections::HashMap;

/// A `SearchSequent` represents a sequent of the form
/// `antecedent_1 & antecedent_2 & ... => consequent_1 | consequent_2 | ...`,
/// where all the metavariables captured (needed) in `consequents` are
/// already captured by the `antecedents`.
///
/// The consequents may refer to metavariables outside their capture
/// (dependency) set: such unbound metavariables represent $$y$ in
/// existentials of the form
/// $$\forall .. p(...) \wedge q(...) => \exists y. r(y, ...)$$.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SearchSequent {
    antecedents: Constraint,
    consequents: BTreeSet<Constraint>,
}

impl SearchSequent {
    /// Constructs a sequent that represents the axiom: "forall
    /// captures such that `antecedents` match currently known facts,
    /// at least one of the `consequents` holds."
    ///
    /// # Errors
    ///
    /// Returns `Err` if one of the `consequents` captures (depends on)
    /// `MetaVar`s not captured by the `antecedents`.
    pub fn new<I: IntoIterator<Item = Constraint>>(
        antecedents: Constraint,
        consequents: I,
    ) -> Result<SearchSequent, &'static str> {
        let mut consequent_set = BTreeSet::new();

        for consequent in consequents {
            if !consequent.captures().is_subset(antecedents.captures()) {
                return Err("Consequent depends on metavars not captured in antecedents.");
            }

            consequent_set.insert(consequent);
        }

        Ok(Self {
            antecedents,
            consequents: consequent_set,
        })
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn antecedents(&self) -> &Constraint {
        &self.antecedents
    }

    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn consequents(&self) -> &BTreeSet<Constraint> {
        &self.consequents
    }
}

/// Constructs a differential dataflow graph for all the `sequents`;
/// the result is a map from right-hand side template to collection
/// of matched captures.
///
/// # Errors
///
/// Returns `Err` when the planned shapes and the `inputs`' shapes
/// conflict.
pub fn enumerate_instantiation_candidates<G, I, H>(
    scope: &mut G,
    sequents: I,
    inputs: &HashMap<String, FactCollection<G>, H>,
) -> Result<HashMap<SearchSequent, CaptureCollection<G>>, &'static str>
where
    G: Input,
    G::Timestamp: Lattice + Ord,
    I: IntoIterator<Item = SearchSequent>,
    H: std::hash::BuildHasher + Clone,
{
    let sources = inputs
        .iter()
        .map(|(pred, col)| (pred.clone(), Source::new(pred, col.shape)))
        .collect::<HashMap<String, _>>();

    let instantiate = |sequent: SearchSequent| {
        let plan = plan_sequent(
            sequent.antecedents(),
            &sequent.consequents().iter().cloned().collect::<Vec<_>>(),
            &sources,
        )?;

        let captures = lower_matching_plan(scope, &mut default_injector, &plan, inputs)?;

        // Compare the captures as ordered lists: this simplifies
        // logic that must match sequents with captures.
        if sequent
            .antecedents
            .captures()
            .iter()
            .cloned()
            .collect::<Vec<_>>()
            != captures.shape
        {
            // This should indicate a planning failure.
            #[cfg(not(tarpaulin_include))]
            return Err("Actual capture shape does not match template");
        }

        Ok((sequent, captures))
    };

    sequents
        .into_iter()
        .map(instantiate)
        .collect::<Result<HashMap<_, _>, _>>()
}

#[test]
fn test_search_sequent_happy_path() {
    use crate::matching::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;

    // Construct a sequent for the axiom
    // p(x, z) -> \exists y s.t. p(x, y) /\ p(y, z),
    // and check that we get the template we expect.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![PredicateFormula::new(
            "p",
            vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
        )],
    )
    .expect("ok");

    let rhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "p",
                vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "p",
                vec![
                    Element::Reference(x.clone()),
                    Element::Reference(y.clone()),
                    Element::Reference(z.clone()),
                ],
            ),
        ],
    )
    .expect("ok");

    SearchSequent::new(lhs, vec![rhs]).expect("ok");
}

#[test]
fn test_search_sequent_missing_capture() {
    use crate::matching::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;

    // Construct a sequent where the left-hand side only captures `x`,
    // and the right-hand side needs `x` *and* `y`.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone()].iter().cloned().collect(),
        vec![PredicateFormula::new(
            "p",
            vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
        )],
    )
    .expect("ok");

    let rhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "p",
                vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "p",
                vec![
                    Element::Reference(x.clone()),
                    Element::Reference(y.clone()),
                    Element::Reference(z.clone()),
                ],
            ),
        ],
    )
    .expect("ok");

    assert!(SearchSequent::new(lhs, vec![rhs.clone()]).is_err());
}

#[test]
fn test_enumerate_candidates_happy_path() {
    use super::sink_all_collections;
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Enumerate instantiation candidates for the axiom
    // p(x, z) -> \exists y s.t. p(x, y) /\ p(y, z).
    //
    // We want to both confirm that we find some instances,
    // and that `p(a, a)` does not trigger instantiation.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let lhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![PredicateFormula::new(
            "p",
            vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
        )],
    )
    .expect("ok");

    let rhs = Constraint::new(
        [x.clone(), z.clone()].iter().cloned().collect(),
        vec![
            PredicateFormula::new(
                "p",
                vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
            ),
            PredicateFormula::new(
                "p",
                vec![Element::Reference(y.clone()), Element::Reference(z.clone())],
            ),
        ],
    )
    .expect("ok");

    let sequent = SearchSequent::new(lhs, vec![rhs.clone()]).expect("ok");
    let key = sequent.clone();

    let sinks: HashMap<SearchSequent, CaptureSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "p".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        let candidates =
            enumerate_instantiation_candidates(scope, vec![sequent], &initial_inputs).expect("ok");

        let ret = sink_all_collections(candidates.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        // This one should not result in any match: if p(2, 2) is true,
        // there already exists a y such that p(2, y) and (y, 2)...
        // y = 2.
        initial.insert([Variable::new(2), Variable::new(2)].into());

        // But this one should result in a capture.
        initial.insert([Variable::new(3), Variable::new(4)].into());
        // As well as that one.
        initial.insert([Variable::new(4), Variable::new(5)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    assert_eq!(sinks.keys().cloned().collect::<Vec<_>>(), vec![key.clone()]);
    assert_eq!(
        sinks.get(&key).expect("found").values::<HashSet<_>>(),
        [
            [Variable::new(3), Variable::new(4)].into(),
            [Variable::new(4), Variable::new(5)].into()
        ]
        .iter()
        .cloned()
        .collect()
    );
}

#[test]
fn test_enumerate_candidates_empty_antecedents() {
    use super::sink_all_collections;
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Enumerate instantiation candidates for the axiom
    // [nothing] -> \exists x, y s.t. p(x, x).
    //
    // We should find a single empty capture.
    let x = MetaVar::new("x");

    let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

    let rhs = Constraint::new(
        BTreeSet::new(),
        vec![PredicateFormula::new(
            "p",
            vec![Element::Reference(x.clone()), Element::Reference(x.clone())],
        )],
    )
    .expect("ok");

    let sequent = SearchSequent::new(lhs, vec![rhs.clone()]).expect("ok");
    let key = sequent.clone();

    let sinks: HashMap<SearchSequent, CaptureSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "p".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        let candidates =
            enumerate_instantiation_candidates(scope, vec![sequent], &initial_inputs).expect("ok");

        let ret = sink_all_collections(candidates.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        // This does not match [x, x], so should not prevent a capture.
        initial.insert([Variable::new(1), Variable::new(2)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    assert_eq!(sinks.keys().cloned().collect::<Vec<_>>(), vec![key.clone()]);
    assert_eq!(
        sinks.get(&key).expect("found").values::<HashSet<_>>(),
        [[].into(),].iter().cloned().collect()
    );
}

#[test]
fn test_enumerate_candidates_empty_antecedents_already_matched() {
    use super::sink_all_collections;
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Enumerate instantiation candidates for the axiom
    // [nothing] -> \exists x, y s.t. p(x, x).
    //
    // We should not find any capture when there already is a fact of
    // the form [x, x].
    let x = MetaVar::new("x");

    let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

    let rhs = Constraint::new(
        BTreeSet::new(),
        vec![PredicateFormula::new(
            "p",
            vec![Element::Reference(x.clone()), Element::Reference(x.clone())],
        )],
    )
    .expect("ok");

    let sequent = SearchSequent::new(lhs, vec![rhs.clone()]).expect("ok");
    let key = sequent.clone();

    let sinks: HashMap<SearchSequent, CaptureSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [(
            "p".into(),
            FactCollection::new(2, initial.to_collection(scope)),
        )]
        .iter()
        .cloned()
        .collect();

        let candidates =
            enumerate_instantiation_candidates(scope, vec![sequent], &initial_inputs).expect("ok");

        let ret = sink_all_collections(candidates.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        // This does match [x, x], so should prevent a capture.
        initial.insert([Variable::new(2), Variable::new(2)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    assert_eq!(sinks.keys().cloned().collect::<Vec<_>>(), vec![key.clone()]);
    assert_eq!(
        sinks.get(&key).expect("found").values::<HashSet<_>>(),
        HashSet::new()
    );
}

#[test]
fn test_enumerate_candidates_two_sequents() {
    use super::sink_all_collections;
    use super::CaptureSink;
    use crate::ground::Variable;
    use crate::matching::PredicateFormula;
    use crate::unification::Element;
    use crate::unification::MetaVar;
    use differential_dataflow::input::InputSession;
    use std::collections::HashSet;

    // Enumerate instantiation candidates for the axioms
    //   p(x, z) -> \exists y s.t. p(x, y) /\ p(y, z)
    // and
    //   -> \exists q(x)
    //
    // We want to confirm that we find the correct instances for both
    // sequents.
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");

    let sequent1 = {
        let lhs = Constraint::new(
            [x.clone(), z.clone()].iter().cloned().collect(),
            vec![PredicateFormula::new(
                "p",
                vec![Element::Reference(x.clone()), Element::Reference(z.clone())],
            )],
        )
        .expect("ok");

        let rhs = Constraint::new(
            [x.clone(), z.clone()].iter().cloned().collect(),
            vec![
                PredicateFormula::new(
                    "p",
                    vec![Element::Reference(x.clone()), Element::Reference(y.clone())],
                ),
                PredicateFormula::new(
                    "p",
                    vec![Element::Reference(y.clone()), Element::Reference(z.clone())],
                ),
            ],
        )
        .expect("ok");

        SearchSequent::new(lhs, vec![rhs.clone()]).expect("ok")
    };

    let sequent2 = {
        let lhs = Constraint::new(BTreeSet::new(), vec![]).expect("ok");

        let rhs = Constraint::new(
            BTreeSet::new(),
            vec![PredicateFormula::new(
                "q",
                vec![Element::Reference(x.clone())],
            )],
        )
        .expect("ok");

        SearchSequent::new(lhs, vec![rhs.clone()]).expect("ok")
    };

    let keys = [sequent1.clone(), sequent2.clone()];
    let sinks: HashMap<SearchSequent, CaptureSink> = timely::execute::example(move |scope| {
        let mut initial = InputSession::new();

        let initial_inputs: HashMap<String, FactCollection<_>> = [
            (
                "p".into(),
                FactCollection::new(2, initial.to_collection(scope)),
            ),
            ("q".into(), FactCollection::new(1, scope.new_collection().1)),
        ]
        .iter()
        .cloned()
        .collect();

        let candidates =
            enumerate_instantiation_candidates(scope, vec![sequent1, sequent2], &initial_inputs)
                .expect("ok");

        let ret = sink_all_collections(candidates.into_iter(), HashMap::new()).expect("ok");

        initial.advance_to(0);
        // This one should not result in any match: if p(2, 2) is true,
        // there already exists a y such that p(2, y) and (y, 2)...
        // y = 2.
        initial.insert([Variable::new(2), Variable::new(2)].into());

        // But this one should result in a capture.
        initial.insert([Variable::new(3), Variable::new(4)].into());
        // As well as that one.
        initial.insert([Variable::new(4), Variable::new(5)].into());
        initial.flush();
        initial.advance_to(1);

        ret
    });

    assert_eq!(
        sinks.keys().cloned().collect::<HashSet<_>>(),
        keys.iter().cloned().collect()
    );

    assert_eq!(
        sinks.get(&keys[0]).expect("found").values::<HashSet<_>>(),
        [
            [Variable::new(3), Variable::new(4)].into(),
            [Variable::new(4), Variable::new(5)].into()
        ]
        .iter()
        .cloned()
        .collect()
    );
    assert_eq!(
        sinks.get(&keys[1]).expect("found").values::<HashSet<_>>(),
        [[].into(),].iter().cloned().collect()
    );
}

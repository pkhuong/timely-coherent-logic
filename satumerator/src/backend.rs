//!
use super::gadgets;
use super::solver_state::SolverState;
use super::solver_state::VariableMeaning;
use super::ChoiceConstraint;
use super::FathomedRegion;
use super::StateAtom;
use cryptominisat::Lbool;
use cryptominisat::Lit;
use std::collections::BTreeSet;
use std::collections::HashSet;

/// The `AssignmentReductionPolicy` determines how we want to handle a
/// "gap" witness or any other partial assignment that is (should be)
/// disjoint from the nogoods.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum AssignmentReductionPolicy {
    /// Don't reduce at all, only check that the input is disjoint
    /// from the nogoods and return it as is.
    Noop,
    /// Check that the input assignment is valid, and stop after using
    /// the conflict information from that one solve.
    OneShot,
    /// Probe each literal in back-to-front order.  The result is
    /// minimal.
    StrictlyInOrder,
    /// Take any hint we can get.  The result is also minimal, but may
    /// remove literals out of order.
    Greedy,
}

pub struct Impl<A: StateAtom> {
    sat_state: SolverState<A>,
    // nogood clauses.
    clauses: HashSet<FathomedRegion<A>>,
    domain: HashSet<ChoiceConstraint<A>>,
}

impl<A: StateAtom> Impl<A> {
    pub fn new() -> Self {
        Self {
            sat_state: SolverState::new(),
            clauses: HashSet::new(),
            domain: HashSet::new(),
        }
    }

    /// Returns an assignment of truth values to atom that is not yet
    /// forbidden by the constraints added to the Satumerator state,
    /// if any.
    ///
    /// A `None` means that the search has been completed.
    pub fn gap_witness(&mut self, policy: AssignmentReductionPolicy) -> Option<Vec<(A, bool)>> {
        use std::convert::TryInto;
        use VariableMeaning::Atom;

        match self.sat_state.exhaustive_checker().solve() {
            Lbool::True => {
                let model: Vec<_> = self.sat_state.exhaustive_checker().get_model().into();
                let mut result = Vec::with_capacity(model.len());

                for (index, value) in model.iter().enumerate() {
                    let bool_value = match value {
                        Lbool::True => true,
                        Lbool::False => false,
                        #[cfg(not(tarpaulin_include))]
                        Lbool::Undef => panic!("Undefined value in model"),
                    };

                    let lit = Lit::new(index.try_into().unwrap(), false).unwrap();
                    if let Some(Atom(atom)) = self.sat_state.meaning(lit) {
                        result.push((atom.clone(), bool_value));
                    }
                }

                if policy == AssignmentReductionPolicy::Noop {
                    Some(result)
                } else {
                    // Reduction can only fail if the input assignment
                    // overlaps with the nogoods, or on timeout.
                    // Overlap is impossible (unless the SAT solver is
                    // broken), so we can always return the initial
                    // witness on error.
                    Some(
                        self.disjoint_from_nogoods(result.clone(), policy)
                            .unwrap_or(result),
                    )
                }
            }
            // If there is no model, then we're done.
            Lbool::False => None,
            #[cfg(not(tarpaulin_include))]
            Lbool::Undef => panic!("Exhaustive check timed out without time limit."),
        }
    }

    /// Determines if `assignment` is such that it and all of its
    /// (valid) extensions aren't covered (forbidden) by a nogood.
    ///
    /// On success, applies the reduction policy to return a smaller
    /// (still disjoint) assignment.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the initial assignment overlaps with the
    /// nogoods, or when the underlying SAT solver times out.
    pub fn disjoint_from_nogoods(
        &mut self,
        assignment: Vec<(A, bool)>,
        reduction_policy: AssignmentReductionPolicy,
    ) -> Result<Vec<(A, bool)>, &'static str> {
        use AssignmentReductionPolicy::{Greedy, Noop, OneShot, StrictlyInOrder};

        let (use_conflict, probe_loop) = match reduction_policy {
            Noop => (false, false),
            OneShot => (true, false),
            // When reducing strictly in order, we can't use
            // `CryptoMiniSat`'s heuristic conflict.
            StrictlyInOrder => (false, true),
            Greedy => (true, true),
        };

        match self.sat_state.tseitin_checker().1 {
            None => Ok(vec![]),
            Some(output) => {
                // Set of literals that we probed and know are
                // necessary for this reduction order.
                let mut mandatory = BTreeSet::new();
                // Current set of non-mendatory assumptions we're
                // trying to reduce.
                let mut candidates = build_assumptions(&mut self.sat_state, assignment);

                // Constructs a new `candidates` vector from a
                // conflict information.
                let update_candidates =
                    |candidates: Vec<Lit>, mandatory: &BTreeSet<Lit>, conflict: BTreeSet<Lit>| {
                        if use_conflict {
                            candidates
                                .into_iter()
                                .filter(|lit| conflict.contains(lit) & !mandatory.contains(lit))
                                .collect::<Vec<Lit>>()
                        } else {
                            candidates
                        }
                    };
                let solver = self.sat_state.tseitin_checker().0;

                // Confirm that the candidates are disjoint from the
                // nogoods.
                {
                    let initial_conflict = find_conflict(solver, output, candidates.clone())?;
                    candidates = update_candidates(candidates, &mandatory, initial_conflict);
                }

                if !probe_loop {
                    return Ok(literals_to_assignment(&mut self.sat_state, candidates));
                }

                while let Some(candidate) = candidates.pop() {
                    // Let's probe and see happens when we don't
                    // assume the last literal in `candidates`.
                    let mut assumptions = candidates.clone();
                    assumptions.extend(mandatory.iter().cloned());

                    match find_conflict(solver, output, assumptions) {
                        // If we're not positive that the candidate is
                        // redundant, mark it as mandatory.
                        Err(_) => {
                            mandatory.insert(candidate);
                        }
                        // We still have a conflict; we don't need the
                        // candidate!
                        Ok(conflict) => {
                            candidates = update_candidates(candidates, &mandatory, conflict);
                        }
                    }
                }

                Ok(literals_to_assignment(
                    &mut self.sat_state,
                    mandatory.into_iter().collect(),
                ))
            }
        }
    }

    /// Refines the domain to take into account the "pick one of k"
    /// choice `constraint`.
    pub fn declare_choice(&mut self, constraint: ChoiceConstraint<A>) {
        if self.domain.contains(&constraint) {
            return;
        }

        let vars: Vec<Lit> = self
            .sat_state
            .atoms_vars(constraint.options.iter().cloned());

        let add_constraint = |solver: &mut _| {
            gadgets::add_at_least_one_constraint(solver, &vars);
            gadgets::add_at_most_one_constraint(solver, &vars);
        };

        add_constraint(self.sat_state.exhaustive_checker());
        add_constraint(self.sat_state.tseitin_checker().0);
        self.domain.insert(constraint);
    }

    /// Adds a nogood for `region`.
    pub fn add_nogood(&mut self, region: FathomedRegion<A>) {
        if self.clauses.contains(&region) {
            return;
        }

        let vars: Vec<Lit> = self
            .sat_state
            .atoms_vars(region.partial_assignment.iter().cloned());

        gadgets::add_nogood(self.sat_state.exhaustive_checker(), &vars);
        let (output, fresh) = self
            .sat_state
            .ensure_var(VariableMeaning::TseitinOutput(region.clone()));
        assert!(fresh);
        gadgets::add_tseitin_nogood(self.sat_state.tseitin_checker().0, output, &vars);
        self.sat_state
            .update_tseitin_output(|solver, current| match current {
                Some((fresh, acc)) => {
                    gadgets::add_tseitin_or(solver, fresh, acc, output);
                    fresh
                }
                None => output,
            });

        self.clauses.insert(region);
    }
}

/// Builds an initial assumption vector for `assignment`.
fn build_assumptions<A: StateAtom>(
    sat_state: &mut SolverState<A>,
    assignment: Vec<(A, bool)>,
) -> Vec<Lit> {
    let mut assumptions = Vec::with_capacity(assignment.len());
    for (atom, value) in assignment {
        let (lit, fresh) = sat_state.ensure_var(VariableMeaning::Atom(atom));

        #[cfg(not(tarpaulin_include))]
        if fresh {
            println!("WARNING: unknown variable found in assignment.");
            continue;
        }

        assumptions.push(if value { lit } else { !lit });
    }

    assumptions
}

/// Attempts to reduce `assumptions`, assuming that `nogood_output` is
/// true.
///
/// Returns a subset of the assumptions literals that does not overlap
/// with the nogoods either.
///
/// # Errors
///
/// Returns `Err` if we failed to definitely find a conflict; in that
/// case, the `assumptions` may or may not overlap with the nogoods.
fn find_conflict(
    tseitin_solver: &mut cryptominisat::Solver,
    nogood_output: Lit,
    mut assumptions: Vec<Lit>,
) -> Result<BTreeSet<Lit>, &'static str> {
    // The output variable is true whenever one of the nogood is
    // violated.  We want to force that to happen.
    assumptions.push(nogood_output);

    match tseitin_solver.solve_with_assumptions(&assumptions) {
        // If we can find a violation, or we don't know,
        // assume the assignment can intersect with
        // nogoods.
        Lbool::True => Err("Assumptions overlap with nogoods"),
        #[cfg(not(tarpaulin_include))]
        Lbool::Undef => Err("Conflict checking timed out"),
        Lbool::False =>
        // The conflict list only includes variables in the
        // assumption, but reports the opposite of their value in
        // the assumption: a conflict is a clause (a nogood
        // internal to the SAT solver) learned from the constraint
        // set, that happens to contradict the assumptions.
        //
        // The conflict is of the form "any solution that includes
        // all of these assignments is invalid;" since it
        // contradicts the assumption, it can only contain
        // literals that are also in the assumption, and each of
        // these literals must have a truth value opposite to that
        // in the assumption.
        //
        // That's why we complement the conflict literal before
        // returning
        {
            Ok(tseitin_solver.get_conflict().iter().map(|x| !*x).collect())
        }
    }
}

fn literals_to_assignment<A: StateAtom>(
    sat_state: &mut SolverState<A>,
    literals: Vec<Lit>,
) -> Vec<(A, bool)> {
    literals
        .into_iter()
        .filter_map(|lit| match sat_state.meaning(lit) {
            Some(VariableMeaning::Atom(atom)) => Some((atom.clone(), !lit.isneg())),
            _ => None,
        })
        .collect()
}

#[test]
fn test_smoke() {
    // Create an empty solver. We should find a trivial witness.
    let mut state = Impl::<String>::new();
    assert_eq!(
        state.gap_witness(AssignmentReductionPolicy::Noop),
        Some(vec![])
    );

    // And we should be able to confirm that the empty assignment is
    // safe to explore without wasting work.
    assert_eq!(
        state.disjoint_from_nogoods(vec![], AssignmentReductionPolicy::Noop),
        Ok(vec![])
    );
}

#[test]
fn test_nogood() {
    // Add nogoods for `x = true` and `y = true`.
    // We should still find one last gap, for `x = y = false`.
    let mut state = Impl::<String>::new();

    state.add_nogood(FathomedRegion::new(vec!["x".into()]));
    state.add_nogood(FathomedRegion::new(vec!["y".into()]));

    let witness = state
        .gap_witness(AssignmentReductionPolicy::Noop)
        .expect("has witness");
    assert_eq!(witness, vec![("x".into(), false), ("y".into(), false)]);
}

#[test]
fn test_duplicate_nogood() {
    // Add nogoods for `x = true` and `y = true` multiple times.
    // We should still find one last gap, for `x = y = false`.
    let mut state = Impl::<String>::new();

    state.add_nogood(FathomedRegion::new(vec!["x".into()]));
    state.add_nogood(FathomedRegion::new(vec!["y".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));
    state.add_nogood(FathomedRegion::new(vec!["y".into()]));

    let witness = state
        .gap_witness(AssignmentReductionPolicy::Noop)
        .expect("has witness");
    assert_eq!(witness, vec![("x".into(), false), ("y".into(), false)])
}

#[test]
fn test_nogood_with_domain() {
    // Add nogoods for `x = true` and `y = true`, and then a domain
    // constraint `exactly_one_of(x, y)`.
    // We should be done.

    let mut state = Impl::<String>::new();

    state.add_nogood(FathomedRegion::new(vec!["x".into()]));
    state.add_nogood(FathomedRegion::new(vec!["y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));

    assert_eq!(state.gap_witness(AssignmentReductionPolicy::Noop), None);
}

#[test]
fn test_nogood_with_duplicate_domain() {
    // Add nogoods for `x = true` and `y = true`, and then a domain
    // constraint `exactly_one_of(x, y)`... twice
    // We should be done.

    let mut state = Impl::<String>::new();

    state.add_nogood(FathomedRegion::new(vec!["x".into()]));
    state.add_nogood(FathomedRegion::new(vec!["y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));

    assert_eq!(state.gap_witness(AssignmentReductionPolicy::Noop), None);
}

#[test]
fn test_nogood_with_multiple_domains() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    //
    // There should be exactly one gap left, for `x = false, y = true,
    // z = true`.

    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));

    let witness = state
        .gap_witness(AssignmentReductionPolicy::Noop)
        .expect("has witness");
    assert_eq!(
        witness,
        vec![("x".into(), false), ("y".into(), true), ("z".into(), true)]
    );

    // Now let's claim we also don't like `y = z = true`.
    state.add_nogood(FathomedRegion::new(vec!["y".into(), "z".into()]));
    // We should be done.
    assert_eq!(state.gap_witness(AssignmentReductionPolicy::Noop), None);
}

#[test]
fn test_reduced_nogood_with_multiple_domains() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    //
    // There should be exactly one gap left, for `x = false, y = true,
    // z = true`, and it is implied by `x = false`.

    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));

    let witness = state
        .gap_witness(AssignmentReductionPolicy::Greedy)
        .expect("has witness");
    assert_eq!(witness, vec![("x".into(), false)]);
}

#[test]
fn test_disjoint_from_nogoods() {
    use std::collections::HashMap;

    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    //
    // There should be exactly one gap left, for `x = false, y = true,
    // z = true`, and we should be able to refine it into `y = z =
    // true`.

    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));

    let witness = state
        .gap_witness(AssignmentReductionPolicy::Noop)
        .expect("has witness");
    let refined = state
        .disjoint_from_nogoods(witness, AssignmentReductionPolicy::OneShot)
        .expect("is disjoint");
    // It would also be possible to have `y = true, z = true`, but
    // that's a more complex clause.
    assert_eq!(
        refined.into_iter().collect::<HashMap<_, _>>(),
        [("x".into(), false)].iter().cloned().collect()
    );
}

#[test]
fn test_disjoint_from_nogoods_refine() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.

    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));

    // `x = true` should fail.
    assert!(state
        .disjoint_from_nogoods(vec![("x".into(), true)], AssignmentReductionPolicy::OneShot)
        .is_err());

    // Let's refine `y = true, z = true`.  We can simplify that to
    // either `y = true` or `z = true`.
    let refined_positive = state
        .disjoint_from_nogoods(
            vec![("y".into(), true), ("z".into(), true)],
            AssignmentReductionPolicy::OneShot,
        )
        .expect("is disjoint");
    assert_eq!(refined_positive.len(), 1);
    assert!(refined_positive[0] == ("y".into(), true) || refined_positive[0] == ("z".into(), true));
}

#[test]
fn test_reduce_disjoint() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));

    // Let's refine `y = true, z = true`.  We can simplify that to
    // either `y = true` or `z = true`.
    let refined_positive = state
        .disjoint_from_nogoods(
            vec![("y".into(), true), ("z".into(), true)],
            AssignmentReductionPolicy::Greedy,
        )
        .expect("is disjoint");
    assert_eq!(refined_positive.len(), 1);
    assert!(refined_positive[0] == ("y".into(), true) || refined_positive[0] == ("z".into(), true));
}

#[test]
fn test_reduce_disjoint_in_order() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["x".into()]));

    // Let's refine `y = true, z = true`.  Since'll always check `z =
    // true` first, this should simplify to `y = true`.
    assert_eq!(
        state
            .disjoint_from_nogoods(
                vec![("y".into(), true), ("z".into(), true)],
                AssignmentReductionPolicy::StrictlyInOrder
            )
            .expect("is disjoint"),
        vec![("y".into(), true)]
    );

    // Same thing, but in the reverse order.
    assert_eq!(
        state
            .disjoint_from_nogoods(
                vec![("z".into(), true), ("y".into(), true)],
                AssignmentReductionPolicy::StrictlyInOrder
            )
            .expect("is disjoint"),
        vec![("z".into(), true)]
    );
}

#[test]
fn test_two_nogoods() {
    // Add domain constraints `exactly_one_of(w, x)`,
    // `exactly_one_of(y, z)`, and nogood `w = true`, `y = true`.
    // That should leave one option, `x = z = true`.

    let mut state = Impl::<String>::new();

    state.declare_choice(ChoiceConstraint::new(vec!["w".into(), "x".into()]));
    state.declare_choice(ChoiceConstraint::new(vec!["y".into(), "z".into()]));
    state.add_nogood(FathomedRegion::new(vec!["w".into()]));
    state.add_nogood(FathomedRegion::new(vec!["y".into()]));

    let witness = state
        .gap_witness(AssignmentReductionPolicy::Noop)
        .expect("has witness");
    assert_eq!(
        witness,
        vec![
            ("w".into(), false),
            ("x".into(), true),
            ("y".into(), false),
            ("z".into(), true)
        ]
    );

    state
        .disjoint_from_nogoods(witness, AssignmentReductionPolicy::OneShot)
        .expect("is disjoint");
    // Just `x = true` isn't enough.
    assert!(state
        .disjoint_from_nogoods(vec![("x".into(), true)], AssignmentReductionPolicy::OneShot)
        .is_err());

    let refined = state
        .disjoint_from_nogoods(
            vec![("x".into(), true), ("z".into(), true)],
            AssignmentReductionPolicy::OneShot,
        )
        .expect("is disjoint");
    assert_eq!(refined, vec![("x".into(), true), ("z".into(), true)]);
}

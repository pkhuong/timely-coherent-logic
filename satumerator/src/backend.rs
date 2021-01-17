//!
use super::gadgets;
use super::solver_state::SolverState;
use super::solver_state::VariableMeaning;
use super::ChoiceConstraint;
use super::FathomedRegion;
use super::StateAtom;
use cryptominisat::Lbool;
use cryptominisat::Lit;
use std::collections::HashSet;

/// The `AssignmentReductionPolicy` determines how we want to handle a
/// "gap" witness.  For now, the only thing we can do is to return
/// that witness as is.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum AssignmentReductionPolicy {
    /// Don't reduce at all.
    Noop,
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
    pub fn gap_witness(&mut self, _policy: AssignmentReductionPolicy) -> Option<Vec<(A, bool)>> {
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

                Some(result)
            }
            // If there is no model, then we're done.
            Lbool::False => None,
            #[cfg(not(tarpaulin_include))]
            Lbool::Undef => panic!("Exhaustive check timed out without time limit."),
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

#[test]
fn test_smoke() {
    // Create an empty solver. We should find a trivial witness.
    let mut state = Impl::<String>::new();
    assert_eq!(
        state.gap_witness(AssignmentReductionPolicy::Noop),
        Some(vec![])
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

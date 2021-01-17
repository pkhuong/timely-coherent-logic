mod backend;
mod gadgets;
mod kb;
mod solver_state;

pub use backend::AssignmentReductionPolicy;
pub use kb::ChoiceConstraint;
pub use kb::FathomedRegion;
pub use kb::StateAtom;
use std::collections::HashSet;

/// A `PositiveSatumerator` handles partial assignments that only
/// include "true" values.
///
/// For this invariant to work, each variable must be part of at least
/// one choice constraint.
pub struct PositiveSatumerator<A: StateAtom> {
    known_variables: HashSet<A>,
    backend: backend::Impl<A>,
}

impl<A: StateAtom> PositiveSatumerator<A> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            known_variables: HashSet::new(),
            backend: backend::Impl::new(),
        }
    }

    /// Converts a list of assignments to a list of atoms that must be
    /// set to true.  The structure of `PositiveSatumerator`
    /// constraints guarantees that we can always drop negative
    /// assignments.
    fn assignment_to_positive_atom_list(assignment: Vec<(A, bool)>) -> Vec<A> {
        assignment
            .into_iter()
            .filter_map(|x| if x.1 { Some(x.0) } else { None })
            .collect()
    }

    /// Converts a list of atoms that must be set to true to a list of
    /// assignments.
    fn positive_atom_list_to_assignment(atoms: Vec<A>) -> Vec<(A, bool)> {
        atoms.into_iter().map(|x| (x, true)).collect()
    }

    /// Returns a list atoms such that setting them all to true is not
    /// yet forbidden by the constraints added to the Satumerator
    /// state, if any.
    ///
    /// A `None` means that the search has been completed.
    #[must_use]
    pub fn gap_witness(&mut self, policy: AssignmentReductionPolicy) -> Option<Vec<A>> {
        let witness = self
            .backend
            .gap_witness(AssignmentReductionPolicy::Noop)
            .map(Self::assignment_to_positive_atom_list)?;
        if policy == AssignmentReductionPolicy::Noop {
            Some(witness)
        } else {
            // If `disjoint_from_nogoods` fails, it must be due to a
            // timeout, and we can always default in the initial
            // witness.
            Some(
                self.disjoint_from_nogoods(witness.clone(), policy)
                    .unwrap_or(witness),
            )
        }
    }

    /// Confirms that `assignment` is disjoint from all nogoods: any
    /// extension of `assignment` that satisfies the domain
    /// constraints does not conflict with a nogood set.
    ///
    /// # Errors
    ///
    /// Returns `Err` if we failed to definitely show disjointedness.
    pub fn disjoint_from_nogoods(
        &mut self,
        assignment: Vec<A>,
        policy: AssignmentReductionPolicy,
    ) -> Result<Vec<A>, &'static str> {
        self.backend
            .disjoint_from_nogoods(Self::positive_atom_list_to_assignment(assignment), policy)
            .map(Self::assignment_to_positive_atom_list)
    }

    /// Refines the domain to take into account the "pick one of k"
    /// choice `constraint`.
    pub fn declare_choice(&mut self, constraint: ChoiceConstraint<A>) {
        for option in &constraint.options {
            self.known_variables.insert(option.clone());
        }

        self.backend.declare_choice(constraint);
    }

    /// Adds a nogood for `region`.
    ///
    /// # Errors
    ///
    /// Returns `Err` when some of the atoms in `region` are not
    /// constrained by a "choice" constraint: we can only guarantee
    /// that we can describe regions to explore with purely positive
    /// partial assignments if every atom is part of such a choice
    /// constraint.
    pub fn add_nogood(&mut self, region: FathomedRegion<A>) -> Result<(), &'static str> {
        if region
            .partial_assignment
            .iter()
            .any(|x| !self.known_variables.contains(x))
        {
            return Err("nogood includes unconstrained variable.");
        }

        self.backend.add_nogood(region);
        Ok(())
    }
}

impl<A: StateAtom> Default for PositiveSatumerator<A> {
    fn default() -> Self {
        Self::new()
    }
}

#[test]
fn test_nogood_no_domain() {
    // Add a nogood for `x = true` without a domain constraint.
    // That should fail.

    let mut pos = PositiveSatumerator::<String>::default();

    assert!(pos
        .add_nogood(FathomedRegion::new(vec!["x".into()]))
        .is_err());
}

#[test]
fn test_nogood_with_domain() {
    // Add nogoods for `x = true` and `y = true`, and then a domain
    // constraint `exactly_one_of(x, y)`.
    // We should be done.

    let mut pos = PositiveSatumerator::<String>::default();

    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    pos.add_nogood(FathomedRegion::new(vec!["x".into()]))
        .expect("ok");
    pos.add_nogood(FathomedRegion::new(vec!["y".into()]))
        .expect("ok");

    assert_eq!(pos.gap_witness(AssignmentReductionPolicy::Noop), None);
}

#[test]
fn test_nogood_with_multiple_domains() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    //
    // There should be exactly one gap left, for `x = false, y = true,
    // z = true`.

    let mut pos = PositiveSatumerator::<String>::default();

    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    pos.add_nogood(FathomedRegion::new(vec!["x".into()]))
        .expect("ok");

    let witness: Vec<String> = pos
        .gap_witness(AssignmentReductionPolicy::Noop)
        .expect("has witness");
    assert_eq!(witness, ["y", "z"]);

    // Now let's claim we also don't like `y = z = true`.
    pos.add_nogood(FathomedRegion::new(vec!["y".into(), "z".into()]))
        .expect("ok");
    // We should be done.
    assert_eq!(pos.gap_witness(AssignmentReductionPolicy::Noop), None);
}

#[test]
fn test_disjoint_from_nogoods() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    //
    // There should be exactly one gap left, for `x = false, y = true,
    // z = true`, and we should be able to refine it into `y = z =
    // true`.

    let mut pos = PositiveSatumerator::<String>::default();

    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    pos.add_nogood(FathomedRegion::new(vec!["x".into()]))
        .expect("ok");

    let witness = pos
        .gap_witness(AssignmentReductionPolicy::Greedy)
        .expect("has witness");
    // `y = true` or `z = true` will work.
    assert!(witness == ["y"] || witness == ["z"]);
}

#[test]
fn test_disjoint_from_nogoods_refine() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.

    let mut pos = PositiveSatumerator::<String>::default();

    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    pos.add_nogood(FathomedRegion::new(vec!["x".into()]))
        .expect("ok");

    // `x = true` should fail.
    assert!(pos
        .disjoint_from_nogoods(vec!["x".into()], AssignmentReductionPolicy::Noop)
        .is_err());

    // Let's refine `y = true, z = true`.  We can simplify that to
    // either `y = true` or `z = true`.
    let refined_positive = pos
        .disjoint_from_nogoods(
            vec!["y".into(), "z".into()],
            AssignmentReductionPolicy::OneShot,
        )
        .expect("is disjoint");
    assert!(refined_positive == ["y"] || refined_positive == ["z"]);
}

#[test]
fn test_reduce_disjoint() {
    // Add domain constraints `exactly_one_of(x, y)`,
    // `exactly_one_of(x, z)`, and nogood `x = true.
    let mut pos = PositiveSatumerator::<String>::default();

    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "y".into()]));
    pos.declare_choice(ChoiceConstraint::new(vec!["x".into(), "z".into()]));
    pos.add_nogood(FathomedRegion::new(vec!["x".into()]))
        .expect("ok");

    // Let's refine `y = true, z = true`.  We can simplify that to
    // either `y = true` or `z = true`.
    let refined_positive = pos
        .disjoint_from_nogoods(
            vec!["y".into(), "z".into()],
            AssignmentReductionPolicy::Greedy,
        )
        .expect("is disjoint");
    assert!(refined_positive == ["y"] || refined_positive == ["z"]);
}

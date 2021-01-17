//!
use super::gadgets;
use super::solver_state::SolverState;
use super::solver_state::VariableMeaning;
use super::{ChoiceConstraint, FathomedRegion, StateAtom};
use cryptominisat::Lit;
use std::collections::HashSet;

pub struct Satumerator<A: StateAtom> {
    clauses: HashSet<FathomedRegion<A>>,
    domain: HashSet<ChoiceConstraint<A>>,
    // When populated, negated_result is set to a variable that is
    // true whenever at least one of the nogoods is violated.
    // It is None only when we have yet to observe a nogood.
    negated_result: Option<Lit>,
    sat_state: SolverState<A>,
}

impl<A: StateAtom> Satumerator<A> {
    pub fn new() -> Self {
        Self {
            clauses: HashSet::new(),
            domain: HashSet::new(),
            negated_result: None,
            sat_state: SolverState::new(),
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
        add_constraint(self.sat_state.positive());
        add_constraint(self.sat_state.negative());

        self.domain.insert(constraint);
    }

    /// Adds a nogood for `region`.
    pub fn note_coverage(&mut self, region: FathomedRegion<A>) {
        if self.clauses.contains(&region) {
            return;
        }

        let vars: Vec<Lit> = self
            .sat_state
            .atoms_vars(region.partial_assignment.iter().cloned());

        gadgets::add_nogood(self.sat_state.positive(), &vars);
        let (output, fresh) = self
            .sat_state
            .ensure_var(Some(VariableMeaning::TseitinOutput(region.clone())));
        assert!(fresh);
        gadgets::add_tseitin_nogood(self.sat_state.negative(), output, &vars);

        self.negated_result = Some(match self.negated_result {
            None => output,
            Some(acc) => {
                let or_result = self.sat_state.ensure_var(None).0;
                gadgets::add_tseitin_or(self.sat_state.negative(), or_result, acc, output);
                or_result
            }
        });
    }
}

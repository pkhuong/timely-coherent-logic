//!
use super::solver_state::SolverState;
use super::StateAtom;
use cryptominisat::Lbool;
use cryptominisat::Lit;

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
}

impl<A: StateAtom> Impl<A> {
    pub fn new() -> Self {
        Self {
            sat_state: SolverState::new(),
        }
    }

    /// Returns an assignment of truth values to atom that is not yet
    /// forbidden by the constraints added to the Satumerator state,
    /// if any.
    ///
    /// A `None` means that the search has been completed.
    pub fn gap_witness(&mut self, _policy: AssignmentReductionPolicy) -> Option<Vec<(A, bool)>> {
        use super::solver_state::VariableMeaning::Atom;
        use std::convert::TryInto;

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

//! In order to represent our search space in CryptoMiniSat, we need a
//! mapping between variable id (u32) and StateAtom, or Tseitin
//! output for a nogood clause.
//!
//! Fun additional complexity: CryptoMiniSat needs us to explicitly
//! register new variables, and we wish to use the same variable id
//! space for both incremental solvers in a Satumerator.
//!
//! We could theoretically use the same instance with a Tseitin
//! encoding for all our SAT needs.  However, the exhaustivity check
//! is correctness critical, so it makes sense to let that check use a
//! tighter, more efficient, encoding that only uses regular
//! incremental solves, without assumptions.
use super::FathomedRegion;
use super::StateAtom;
use cryptominisat::Lit;
use cryptominisat::Solver;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum VariableMeaning<A: StateAtom> {
    Atom(A),
    TseitinOutput(FathomedRegion<A>),
}

pub struct SolverState<A: StateAtom> {
    from_id: Vec<Option<VariableMeaning<A>>>,
    to_id: HashMap<VariableMeaning<A>, Lit>,
    positive: Solver,
    negative: Solver,
}

/// A VariableMap owns a pair of CryptoMiniSat solvers, and maintains
/// a mapping between variable id and what they mean, while creating
/// new variables on demand.
impl<A: StateAtom> SolverState<A> {
    /// Returns a fresh `SolverState` instance.
    pub fn new() -> Self {
        Self {
            from_id: Vec::new(),
            to_id: HashMap::new(),
            positive: Solver::new(),
            negative: Solver::new(),
        }
    }

    /// Returns a `Lit`eral for every `Item` in `wanted`.
    pub fn atoms_vars<Iter, Result>(&mut self, wanted: Iter) -> Result
    where
        Iter: IntoIterator<Item = A>,
        Result: std::iter::FromIterator<Lit>,
    {
        wanted
            .into_iter()
            .map(|atom| self.ensure_var(Some(VariableMeaning::Atom(atom))).0)
            .collect::<Result>()
    }

    /// Returns a variable for `wanted`.  If `wanted` is `None`,
    /// always returns a fresh variable.  Otherwise, returns a
    /// pre-existing variable when there already exists one for
    /// the `wanted` meaning.
    ///
    /// Returns a pair of `(variable, freshly_created?)`.
    pub fn ensure_var(&mut self, wanted: Option<VariableMeaning<A>>) -> (Lit, bool) {
        match wanted {
            Some(meaning) => {
                if let Some(id) = self.to_id.get(&meaning) {
                    return (*id, false);
                }

                let var = self.new_var(Some(meaning.clone()));
                self.to_id.insert(meaning, var);
                (var, true)
            }

            None => (self.new_var(None), true),
        }
    }

    /// Returns the meaning associated with `var`, if any.
    pub fn meaning(&self, var: Lit) -> Option<&VariableMeaning<A>> {
        match self.from_id.get(var.var() as usize) {
            Some(Some(ret)) => Some(&ret),
            _ => None,
        }
    }

    /// Returns the positive solver.
    pub fn positive(&mut self) -> &mut Solver {
        &mut self.positive
    }

    /// Returns the negative solver.
    pub fn negative(&mut self) -> &mut Solver {
        &mut self.negative
    }

    /// Creates a new variable in both solvers, and registers it in
    /// `from_id`.
    fn new_var(&mut self, wanted: Option<VariableMeaning<A>>) -> Lit {
        assert!(self.from_id.len() >= self.to_id.len());
        assert_eq!(self.from_id.len(), self.positive.nvars() as usize);
        assert_eq!(self.from_id.len(), self.negative.nvars() as usize);

        let var = self.positive.new_var();
        let negative_var = self.negative.new_var();
        assert_eq!(var, negative_var);
        assert_eq!(var.var() as usize, self.from_id.len());

        self.from_id.push(wanted);
        var
    }
}

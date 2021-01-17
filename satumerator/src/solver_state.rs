//! In order to represent our search space in `CryptoMiniSat`, we need
//! a mapping between variable id (`u32`) and `StateAtom`.
//!
//! Fun additional complexity: `CryptoMiniSat` needs us to explicitly
//! register new variables, and we wish to use the same variable id
//! space for both incremental solvers in a `Satumerator`.
//!
//! We could theoretically use the same instance with a Tseitin
//! encoding for all our SAT needs.  However, the exhaustivity check
//! is correctness critical, so it makes sense to let that check use a
//! tighter, more efficient, encoding that only uses regular
//! incremental solves, without assumptions.
use super::StateAtom;
use cryptominisat::Lit;
use cryptominisat::Solver;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum VariableMeaning<A: StateAtom> {
    Atom(A),
}

pub struct SolverState<A: StateAtom> {
    from_id: Vec<Option<VariableMeaning<A>>>,
    to_id: HashMap<VariableMeaning<A>, Lit>,
    exhaustive_checker: Solver,
}

/// A `SolverState` owns a `CryptoMiniSat` solver, and maintains a
/// mapping between variable id and what they mean, while creating new
/// variables on demand.
impl<A: StateAtom> SolverState<A> {
    /// Returns a fresh `SolverState` instance.
    #[must_use]
    pub fn new() -> Self {
        Self {
            from_id: Vec::new(),
            to_id: HashMap::new(),
            exhaustive_checker: Solver::new(),
        }
    }

    /// Returns a `Lit`eral for every `Atom` in `wanted`.
    pub fn atoms_vars<Iter, Result>(&mut self, wanted: Iter) -> Result
    where
        Iter: IntoIterator<Item = A>,
        Result: std::iter::FromIterator<Lit>,
    {
        wanted
            .into_iter()
            .map(|atom| self.ensure_var(VariableMeaning::Atom(atom)).0)
            .collect::<Result>()
    }

    /// Finds a variable for `wanted`.
    ///
    /// Returns a pair of `(variable, freshly_created?)`.
    pub fn ensure_var(&mut self, wanted: VariableMeaning<A>) -> (Lit, bool) {
        if let Some(id) = self.to_id.get(&wanted) {
            return (*id, false);
        }

        let var = self.new_var(Some(wanted.clone()));
        self.to_id.insert(wanted, var);
        (var, true)
    }

    /// Returns the meaning associated with `var`, if any.
    pub fn meaning(&self, var: Lit) -> Option<&VariableMeaning<A>> {
        match self.from_id.get(var.var() as usize) {
            Some(Some(ret)) => Some(&ret),
            _ => None,
        }
    }

    /// Returns the exhaustive checking solver.
    #[cfg(not(tarpaulin_include))]
    pub fn exhaustive_checker(&mut self) -> &mut Solver {
        &mut self.exhaustive_checker
    }

    /// Creates a new variable in both solvers, and registers it in
    /// `from_id`.
    fn new_var(&mut self, wanted: Option<VariableMeaning<A>>) -> Lit {
        self.check_rep();

        let var = self.exhaustive_checker.new_var();
        assert_eq!(var.var() as usize, self.from_id.len());

        self.from_id.push(wanted);
        self.check_rep();
        var
    }

    /// Checks internal invariants.
    fn check_rep(&self) {
        assert!(self.from_id.len() >= self.to_id.len());
        assert_eq!(self.from_id.len(), self.exhaustive_checker.nvars() as usize);
    }
}

#[test]
fn solver_state_generate_fresh_vars() {
    use VariableMeaning::Atom;

    let mut state = SolverState::<String>::new();
    let (foo, fresh) = state.ensure_var(Atom("foo".into()));
    assert!(fresh);

    let (bar, fresh2) = state.ensure_var(Atom("bar".into()));
    assert!(fresh2);

    assert_ne!(foo, bar);
    assert_eq!(state.meaning(foo), Some(&Atom("foo".into())));
    assert_eq!(state.meaning(bar), Some(&Atom("bar".into())));
    // No such variable.
    assert_eq!(state.meaning(Lit::new(42, false).expect("ok")), None);
}

#[test]
fn solver_state_reuse_vars() {
    use VariableMeaning::Atom;

    let mut state = SolverState::<String>::new();
    let (foo, fresh) = state.ensure_var(Atom("foo".into()));
    assert!(fresh);

    let (foo2, fresh2) = state.ensure_var(Atom("foo".into()));
    assert!(!fresh2);

    assert_eq!(foo, foo2);
}

#[test]
fn solver_state_atoms_vars() {
    use VariableMeaning::Atom;

    let mut state = SolverState::<String>::new();
    let vars1: Vec<_> = state.atoms_vars(vec!["foo".into(), "bar".into()]);

    let vars2: Vec<_> = state.atoms_vars(vec!["foo".into(), "bar".into()]);

    assert_eq!(vars1, vars2);
    assert_eq!(vars1[0], state.ensure_var(Atom("foo".into())).0);
    assert_eq!(state.meaning(vars1[1]), Some(&Atom("bar".into())));
}

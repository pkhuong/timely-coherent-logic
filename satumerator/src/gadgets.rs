//! We must translate out high-level constraints (e.g., "at most one
//! of these must be true") to CNF clauses in order to use SAT.  This
//! module handles that translation.
use cryptominisat::Lit;
use cryptominisat::Solver;

/// Add a nogood for `vars`.
pub fn add_nogood(solver: &mut Solver, nogood: &[Lit]) {
    // We don't want solutions where all the literals are satisfied.
    // In other words, at least one of them must be violated, i.e.
    // at least one of their complements must be true.
    solver.add_clause(&nogood.iter().map(|x| !*x).collect::<Vec<_>>());
}

#[test]
fn test_nogood() {
    use cryptominisat::Lbool;

    let mut solver = Solver::new();
    let (x, y, z) = (solver.new_var(), solver.new_var(), solver.new_var());

    // Add a nogood for (x, y, z)
    add_nogood(&mut solver, &[x, y, z]);

    // The constraint set is feasible.
    assert_eq!(solver.solve(), Lbool::True);
    // Iterate over the truth value for all 3 variables
    for values in 0..8 {
        let x_value = (values & 1) != 0;
        let y_value = (values & 2) != 0;
        let z_value = (values & 4) != 0;
        let assumptions = [
            Lit::new(x.var(), !x_value).expect("ok"),
            Lit::new(y.var(), !y_value).expect("ok"),
            Lit::new(z.var(), !z_value).expect("ok"),
        ];
        // Should be true if `values != 7` (if variables not all true).
        let expected = if values == 7 {
            Lbool::False
        } else {
            Lbool::True
        };

        println!(
            "values={} assumptions={:?} expected={:?}",
            values, assumptions, expected
        );
        assert_eq!(solver.solve_with_assumptions(&assumptions), expected);
    }
}

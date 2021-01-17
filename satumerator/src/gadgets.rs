//! We must translate out high-level constraints (e.g., "at most one
//! of these must be true") to CNF clauses in order to use SAT.  This
//! module handles that translation, including the Tseitin aproach
//! with auxiliary variables for complemented nogoods.
use cryptominisat::Lit;
use cryptominisat::Solver;

/// Forces at least one of `vars` to be true.
pub fn add_at_least_one_constraint(solver: &mut Solver, vars: &[Lit]) {
    solver.add_clause(vars);
}

/// Forces at most one of `vars` to be true.  
pub fn add_at_most_one_constraint(solver: &mut Solver, vars: &[Lit]) {
    for (i, x) in vars.iter().enumerate() {
        for y in vars.split_at(i + 1).1 {
            // For each pair of variable, both variables can't be
            // true, i.e., at least one must be false.
            solver.add_clause(&[!*x, !*y]);
        }
    }
}

/// Add a nogood for `vars`.  
pub fn add_nogood(solver: &mut Solver, nogood: &[Lit]) {
    // We don't want solutions where all the literals are satisfied.
    // In other words, at least one of them must be violated, i.e.
    // at least one of their complements must be true.
    solver.add_clause(&nogood.iter().map(|x| !*x).collect::<Vec<_>>());
}

/// Constrains `output = (var_0 & var_1 & ...)`.
/// Output is true iff the model is rejected by the nogood.
pub fn add_tseitin_nogood(solver: &mut Solver, output: Lit, nogood: &[Lit]) {
    // For each var in nogood, `output -> var`, i.e., `!output | var`.
    for var in nogood {
        solver.add_clause(&[*var, !output]);
    }

    // Similarly, `nogood -> output`, i.e., `!nogood | output`,
    // and we can apply De Morgan's law on `!nogood`
    let mut one_of = Vec::with_capacity(nogood.len() + 1);
    one_of.push(output);
    for var in nogood {
        one_of.push(!*var);
    }

    solver.add_clause(&one_of);
}

/// Constraints `output = x | y`.
pub fn add_tseitin_or(solver: &mut Solver, output: Lit, x: Lit, y: Lit) {
    // x -> output, y -> output;
    // x -> output == !x | output.
    solver.add_clause(&[!x, output]);
    solver.add_clause(&[!y, output]);
    //    output -> x | y
    // == !output | x | y
    solver.add_clause(&[!output, x, y]);
}

#[test]
fn test_add_at_least_one() {
    use cryptominisat::Lbool;

    let mut solver = Solver::new();
    let (x, y, z) = (solver.new_var(), solver.new_var(), solver.new_var());

    add_at_least_one_constraint(&mut solver, &[x, y, z]);

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
        let expected = if x_value | y_value | z_value {
            Lbool::True
        } else {
            Lbool::False
        };

        println!(
            "values={} assumptions={:?} expected={:?}",
            values, assumptions, expected
        );
        assert_eq!(solver.solve_with_assumptions(&assumptions), expected);
    }
}

#[test]
fn test_add_at_most_one() {
    use cryptominisat::Lbool;

    let mut solver = Solver::new();
    let (x, y, z) = (solver.new_var(), solver.new_var(), solver.new_var());

    add_at_most_one_constraint(&mut solver, &[x, y, z]);

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
        // Should be true if `popcount(values) <= 1`
        let expected = if (values & (values - 1)) == 0 {
            Lbool::True
        } else {
            Lbool::False
        };

        println!(
            "values={} assumptions={:?} expected={:?}",
            values, assumptions, expected
        );
        assert_eq!(solver.solve_with_assumptions(&assumptions), expected);
    }
}

#[test]
fn test_no_good() {
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
        // Should be true if `values != 7`
        let expected = if values != 7 {
            Lbool::True
        } else {
            Lbool::False
        };

        println!(
            "values={} assumptions={:?} expected={:?}",
            values, assumptions, expected
        );
        assert_eq!(solver.solve_with_assumptions(&assumptions), expected);
    }
}

#[test]
fn test_tseitin_no_good() {
    use cryptominisat::Lbool;

    let mut solver = Solver::new();
    let (r, x, y, z) = (
        solver.new_var(),
        solver.new_var(),
        solver.new_var(),
        solver.new_var(),
    );

    // Add r == (x & y & z)
    add_tseitin_nogood(&mut solver, r, &[x, y, z]);
    // The constraint set is feasible.
    assert_eq!(solver.solve(), Lbool::True);
    // Iterate over the truth value for all 3 variables
    for values in 0..16 {
        let r_value = (values & 1) != 0;
        let x_value = (values & 2) != 0;
        let y_value = (values & 4) != 0;
        let z_value = (values & 8) != 0;
        let assumptions = [
            Lit::new(r.var(), !r_value).expect("ok"),
            Lit::new(x.var(), !x_value).expect("ok"),
            Lit::new(y.var(), !y_value).expect("ok"),
            Lit::new(z.var(), !z_value).expect("ok"),
        ];
        let expected = if r_value == (x_value & y_value & z_value) {
            Lbool::True
        } else {
            Lbool::False
        };

        println!(
            "values={} assumptions={:?} expected={:?}",
            values, assumptions, expected
        );
        assert_eq!(solver.solve_with_assumptions(&assumptions), expected);
    }
}

#[test]
fn test_tseitin_or() {
    use cryptominisat::Lbool;

    let mut solver = Solver::new();
    let (r, x, y) = (solver.new_var(), solver.new_var(), solver.new_var());

    // Let r = x | y
    add_tseitin_or(&mut solver, r, x, y);

    // The constraint set is feasible.
    assert_eq!(solver.solve(), Lbool::True);
    // Iterate over the truth value for all 3 variables
    for values in 0..8 {
        let r_value = (values & 1) != 0;
        let x_value = (values & 2) != 0;
        let y_value = (values & 4) != 0;
        let assumptions = [
            Lit::new(r.var(), !r_value).expect("ok"),
            Lit::new(x.var(), !x_value).expect("ok"),
            Lit::new(y.var(), !y_value).expect("ok"),
        ];
        // Should be true if `values != 7`
        let expected = if r_value == (x_value | y_value) {
            Lbool::True
        } else {
            Lbool::False
        };

        println!(
            "values={} assumptions={:?} expected={:?}",
            values, assumptions, expected
        );
        assert_eq!(solver.solve_with_assumptions(&assumptions), expected);
    }
}

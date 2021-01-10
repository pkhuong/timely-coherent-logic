Satumerator: exhaustive enumeration with SAT
============================================

Discrete search solvers often implement implicit enumeration
algorithms like best-first or depth-first branch-and-bound because
it's hard to know when more complex strategies are done.

Satumerator answers that and other related questions by deferring to
the incremental SAT solver
[CryptoMiniSat](https://github.com/msoos/cryptominisat).

Model
-----

The design of Satumerator assumes that the caller is exploring a
discrete, but not necessarily finite, domain.  The search tree may
have unbounded depth, but each node must have finite but
otherwise unbounded (up to machine limits) arity... a
[lazy rose tree](https://en.wikipedia.org/wiki/Rose_tree) would
be one way to represent the search tree.  Moreover, each arc at a node
is associated with a state refinement, an assignment of truth values
to a set of variables, rather than a history or trace: this Markovian
assumption (what matters is the current state, or partial assignment,
not how we got there) is key to the enumerator approach.

The Satumerator knowledge base is initially empty, with an
[open-world assumption](https://en.wikipedia.org/wiki/Open-world_assumption),
and contains information about atomic conditions like "the door is
open" with a truth value.  Satumerator internally maps each such
opaque condition to a SAT variable; domain constraints let us
construct n-ary choices on top of there binary conditions.

At any point, a caller may add information in two ways:

1. A domain constraint refines the set of search states we're
   interested in, by constraining atomic conditions.  For example, one
   could add that exactly one of "the door is open" or "the window is
   open" must be true (but potentially irrelevant) in each state.
2. A fathomed (nogood) clause declares that we have explored every
   state that satisfies the conjunctive clause (e.g., we might have
   fathomed all states corresponding to "the door is open and the
   window is closed").  This declaration includes states with
   variables (e.g., "the lights are on") absent from the clause, or
   even not yet mentioned when the clause was added.

Satumerator only supports domain constraints of the form "at least one
of x, y, ..." must be known to be true, or "at most one of, x, y,
..." must be known to be true... or both at the same time, i.e.,
"exactly one of x, y, ..." must be known to be true.

The latter "exactly one" constraints are special; we'll see how they
let us support more restricted search algorithms where only positive
choices (`x = true`) may be made explicitly, and all negative choices
(`x = false`) must be implicitly derived from another positive choice.

Fathomed clauses must be conjunctions of atomic conditions like "the
door is open", and "the window is closed."  In most cases, these
conjunctions will only include atomic conditions positively (known to
be true), but we also support negative conditions, which lets us
encode information like "any state where the door is not known to be
open has already been explored."

We never have to explicit declare atomic conditions (variables):
variables are only useful once they appear in a constraint or a
fathomed clause.  Thanks to the open world assumption, we are also
free to define domain constraints lazily: the worst that can happen is
we'll consider assignments that actually aren't in the domain.

Queries
-------

Given a Satumerator's current knowledge base, it can answer three
types of queries.

The first query, "Exhaustive," asks whether the fathomed clauses in
the knowledge base exhaustively cover the set of potential states
defined by the domain constraints and by a partial assignment (initial
state).  On success, the search is done.  On failure, Satumerator
offers a proof witness: a state (partial assignment of variables) that
satisfies the domain constraints but isn't covered by any of the
fathomed clauses.  The witness for an empty knowledge base may be
surprising: the open world assumption means that the empty partial
assignment isn't fathomed.

The second query, "Overlap," asks whether a partial assignment (set of
conditions known to be true or false) overlaps with the search space
already fathomed.  Overlap is a weaker condition than containment, and
helps us guarantee that a search will never be fully redundant.  The
witness returned by a failed "Exhaustive" query never overlaps with
the fathomed search space.

Finally, the third query, "Reduce," a convenience wrapper around
"Overlap," accepts a valid state that must not overlap with
the fathomed search space, and returns a new smaller state (i.e.,
larger search subspace).

As a special case for "Reduce," one may also ask for a partial
assignment that only includes variables set to true.  When every
decision variable is part of an "exactly one" domain constraint,
this simplification is always possible.

Conditional fathoming
---------------------

Search trees are often impractically deep, if not infinitely so.  In
such cases, we may want to mark a region (partial assignment) as
explored *because we gave up* before completing the exploration.

With such "given up" clauses, we'll want to avoid corresponding
regions of the search space when deciding where to look next.
However, when we find that the whole search space is covered by
clauses, we also want to determine whether actually fathomed clauses
suffice for full coverage, or whether we're instead merely "done"
because we gave up.

We support this use case by optionally tagging clauses with a
condition; all queries can now also specify a set of conditions
that must be obeyed.

For example, a depth-bounded search might tag a clause with the "depth
<= 4" condition.  Once all search subtrees of depth at most 4 have
been explored (fathomed or given up), the search can either stop,
or ignore "depth <= 4" clauses and increase the search depth.

Optimisation: the final frontier
--------------------------------

Satumerator does not support currently support optimisation: it
targets pure satisfaction problems (e.g., proof search).  However,
there is a clear connection between Benders decomposition and the
nogood search approach.  In order to make that connection more
concrete, we must add two capabilities, one heuristic and the other
crucial for correctness.

The heuristic component is a primal optimiser when generating or
reducing states.  We might want to somehow approximate the objective
function in our internal SAT formulation, in order to steer witnesses
for "Exhaustive" queries toward interesting (low "cost") solutions.
Similarly, when reducing an assignment, we may want to focus on
partial assignments with a lower cost estimate.  There's a lot of
"maybe" and "might" in the current paragraph: search heuristics are
just that, and what works on one class of problems may not be
appropriate for another.

In contrast to the search prioritisation heuristics, fathoming by
objective value bound *must be correct*.  Assume we have a bound on
the best feasible solution, which may improve over the course of the
search.  We will now include a third type of information, in
conjunction with this best primal bound: optimistic (lower) bound
functions from partial assignments to objective (cost) value.

In Benders decomposition, these bound functions are affine
functions; one can generate bounds in discrete problems by looking at
the dual multipliers (shadow costs) for the fixing constraints in
relaxed subproblems, as in
[classic Benders decomposition](https://en.wikipedia.org/wiki/Benders_decomposition),
or,
[more generally](https://optimization.mccormick.northwestern.edu/index.php/Generalized_Benders_decomposition_(GBD)), [with Lagrange multipliers](https://scholar.google.com/scholar?cluster=359718947556852253).

In theory, the bound functions `b(x)` can take any functional form, as
long as our new improved Satumerator can generate valid inequalities
for the corresponding generalised 0/1 knapsack constraint `b(x) <= z*`,
where `z*` is the value of the best primal (feasible) solution so far.

In practice, it's much easier to separate linear knapsack constraints
than everything else, so we'll probably want to stick to affine bound
functions.

It's also not *necessary* to tightly capture the feasible domain of
each knapsack constraint: we can always add pointed domain constraints
on demand.

As with conditional fathoming, it may be useful to tag upper bound
values and optimistic lower bound functions with conditions.
Enforcing aggressive upper bound values helps implement an approximate
best-first search, and approximate lower bound functions can steer the
search towards feasible solutions of higher quality, when we have too
few *exact* lower bounds.

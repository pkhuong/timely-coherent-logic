Propagation core of a coherent logic solver
===========================================

Timely coherent propagator implements the deduction rules for Coherent
Logic on top of differential dataflow.  There is no search component
in the propagator: any choice (i.e., consequent with a disjunction or
existentials) is merely reported to the caller.

The propagator can nevertheless saturate trivial rules, like
commutativity or transitive closures, thanks to its internal datalog
component.

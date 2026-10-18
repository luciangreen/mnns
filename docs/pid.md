# PID analysis

`mnn_pid:analyze_program/2` classifies predicates as recursive or
non-recursive using the program call graph. `mnn_pid:analyze_measures/2`
reports non-recursive predicates separately and recognizes one conservative
termination-measure subset: every direct self-recursive call must pass a strict
subterm of the same compound-pattern argument. This includes list tails and
nested compound subterms. A result such as
`measure(structural(2), Obligations)` identifies the argument and records the
recursive clause and call for each checked decrease.

The measure analysis does not claim full termination. Mutual recursion,
arithmetic measures, unbound arguments, and recursive calls that do not use a
strict subterm of the identified argument are reported as unavailable. The
analysis does not yet produce induction proofs or check a user-supplied
specification.

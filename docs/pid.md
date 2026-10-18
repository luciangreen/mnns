# PID analysis

`mnn_pid:analyze_program/2` classifies predicates as recursive or
non-recursive using the program call graph. `mnn_pid:analyze_measures/2`
reports non-recursive predicates separately and recognizes one conservative
termination-measure subset: every recursive call within a strongly connected
component must pass a strict subterm of the same argument position. This covers
direct recursion and mutually recursive predicates with a shared structural
measure, including list tails and nested compound subterms. A result such as
`measure(structural(2), Obligations)` identifies the argument and records the
recursive clause and call for each checked decrease. The component is accepted
only when every call between its predicates decreases; calls outside the
component are not treated as recursive.

It also recognizes a narrow natural-number pattern: the clause must test
`integer(N)` and `N > 0`, then compute `N1 is N - K` for a positive integer
constant `K`, and recurse directly on `N1`. These four goals must occur in that
order in a conjunction; this restriction ensures the guards hold before the
decrease and excludes unbound and non-integer inputs. The same argument position
and decrease pattern are checked across every recursive call in a mutually
recursive component before a shared natural measure is reported.

The measure analysis does not claim full termination. Mutual recursion without
a shared structural or guarded natural decrease, other arithmetic measures,
unbound arguments, and recursive calls that do not match a supported decrease
pattern are reported as unavailable. It does not yet produce full induction
proofs or check a user-supplied specification.

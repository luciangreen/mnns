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

`mnn_pid:analyze_induction/2` builds on the checked measure results and emits
symbolic clause obligations as `pid_induction_report/1`. Each obligation keeps
the clause ID, head and body, and lists an `induction_hypothesis(Call, Measure)`
for each recursive call. Base clauses therefore have an empty hypothesis list;
mutually recursive calls use the shared component measure. These are templates
for later property proofs, not proofs of a user-supplied specification.

`mnn_pid:analyze_tail_recursion/2` reports `tail_recursive` when every recursive
call in a predicate is in syntactic tail position, and otherwise returns the
offending calls as `non_tail_recursive([recursive_call(ClauseId, Call), ...])`.
Predicates outside recursive call cycles are reported as `non_recursive`.
Conjunctions after a recursive call and calls in negation or an if-then-else
condition are not tail calls; calls in the final goal or a final control-flow
branch can be. The analysis is syntactic: it does not prove stack behavior,
termination, or safety of meta-calls, and inherits the call-graph limitations of
the IR analyses.

Run PID tests alone from the repository root with:

```sh
swipl -q -g "load_files('tests/pid_tests.pl'), run_tests(mnn_pid), halt"
```

Run all tests with `swipl -q -s tests/run.pl`.

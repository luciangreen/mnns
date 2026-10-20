# AIOC structural size metric

`mnn_aioc_size:measure_program_size/2` reports structural counts for an
`mnn_program/5`:

```prolog
program_size(clauses(ClauseCount),
             goals(GoalCount),
             predicates(PredicateCount),
             term_nodes(TermNodeCount),
             weighted_total(WeightedTotal))
```

Each predicate record and clause record contributes one to its corresponding
count. Goal counts include each normalized goal and each control-flow node:
conjunction, disjunction, if-then-else, negation, and `once/1`; `true` and
`fail` each count as one goal. Term-node counts cover each clause head and body.
Variables contribute zero nodes, while each atomic or compound term contributes
one node, in addition to the nodes in its arguments. The weighted total sums
the four reported counts with weight one for each.

This is a deterministic representation-size metric, not an inference-count,
runtime, or memory estimate. It does not establish equivalence, assess candidate
quality, simplify programs, or incorporate them into a library. These broader
AIOC capabilities remain future work; see [`PROGRESS.md`](../PROGRESS.md).
The initial proof-checked bundle writer and verifier are described in
[`bundle.md`](bundle.md).

Run its focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/aioc_size_tests.pl'), run_tests(mnn_aioc_size), halt"
```

Run all test groups, including this one, with:

```sh
swipl -q -s tests/run.pl
```

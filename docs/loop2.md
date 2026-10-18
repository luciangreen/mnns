# loop2 — findall to deterministic loops

`mnn_loop2:convert_program/3` converts supported `findall/3` goals in an MNN
program and returns a `loop2_report/1`.

The current supported subset is deliberately narrow: the generator must be a
direct call to a predicate whose clauses are all ground facts, optionally
followed by arithmetic comparisons in a conjunction. Supported comparisons are
`>`, `>=`, `<`, `=<`, `=:=`, and `=\=`. Their arithmetic expressions may use
numeric constants, unary `+`, `-`, `abs`, and binary `+`, `-`, `*`, `/`, `//`,
`mod`, and `rem`. Filter variables must be bound by the fact call; each
successful template instance must be ground. The converter interprets only this
whitelisted arithmetic subset and does not execute arbitrary filter goals.

The converter materializes the ordered template values that pass the filters
and replaces the goal with a call to a fresh, deterministic recursive list-copy
loop. It preserves source predicates and clause order. Unsupported generators,
rules, built-ins, arbitrary filter predicates, unbound arithmetic, and
generators with variable-valued templates remain unchanged.

Each conversion report cites the `findall_to_fold` lemma and records the
finite-ground-fact, safe-arithmetic-filter, and deterministic-loop side
conditions. The report is an obligation, not a checked proof: the independent
proof checker does not yet validate this loop2 rule. Do not treat converted
output as proof-certified.

Run the full suite, including loop2 tests, with:

```sh
swipl -q -s tests/run.pl
```

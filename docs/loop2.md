# loop2 — findall to deterministic loops

`mnn_loop2:convert_program/3` converts supported `findall/3` goals in an MNN
program and returns a `loop2_report/1`.

The current supported subset is deliberately narrow:

- A direct call to a predicate whose clauses are all ground facts, optionally
  followed by arithmetic comparisons in a conjunction.
- `member/2` over a ground proper list, optionally followed by arithmetic
  comparisons. List order and duplicate elements are preserved.
- `between/3` with integer literal bounds and a variable or integer third
  argument, optionally followed by arithmetic comparisons. Ranges of at most
  10,000 values are converted; larger ranges are left unchanged. Reversed
  bounds convert to an empty result.

Supported comparisons are `>`, `>=`, `<`, `=<`, `=:=`, and `=\=`. Their
arithmetic expressions may use numeric constants, unary `+`, `-`, `abs`, and
binary `+`, `-`, `*`, `/`, `//`, `mod`, and `rem`. Filter variables must be
bound by the generator, and each successful template instance must be ground.
The converter interprets only this whitelisted arithmetic subset and does not
execute arbitrary filter goals.

The converter materializes the ordered template values that pass the filters
and replaces the goal with a call to a fresh, deterministic recursive list-copy
loop. It preserves source predicates and clause order. Unsupported generators,
rules, other built-ins, arbitrary filter predicates, unbound arithmetic, and
generators with variable-valued templates remain unchanged. `between/3` with
non-ground or non-integer bounds, or ranges above the limit, also remains
unchanged.

Each conversion report cites the `findall_to_fold` lemma and records the
finite-ground-fact, safe-arithmetic-filter, and deterministic-loop side
conditions. The report is an obligation, not a checked proof: the independent
proof checker does not yet validate this loop2 rule. Do not treat converted
output as proof-certified.

Run the full suite, including loop2 tests, with:

```sh
swipl -q -s tests/run.pl
```

Run just the loop2 tests with:

```sh
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
```

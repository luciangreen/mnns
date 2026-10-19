# loop2 — findall to deterministic loops

`mnn_loop2:convert_program/3` converts supported `findall/3` goals in an MNN
program and returns a `loop2_report/1`.

The current supported subset is deliberately narrow:

- A supported `findall/3` may occur inside conjunction, disjunction,
  if-then-else, negation, or `once/1`; these normalized control structures are
  preserved while conversion traverses their goals.
- A direct call to a predicate whose clauses are all ground facts, including
  calls with bound or partially instantiated arguments, optionally followed by
  arithmetic comparisons in a conjunction. Each fact is matched against a copy
  of the call, so nonmatching facts are excluded and source order is preserved.
- A call to a finite, acyclic chain of facts and rules. Rule bodies may use
  conjunction, disjunction, `true`, `fail`, other supported source-predicate
  calls, and supported arithmetic comparisons. Clause order and answer order
  are preserved, including answers from multi-clause rules. Bound or partially
  instantiated arguments on the generator call are matched against rule heads
  and act as filters.
- `member/2` over a ground proper list, optionally followed by arithmetic
  comparisons. List order and duplicate elements are preserved.
- `select/3` over a ground proper list, optionally followed by arithmetic
  comparisons. Selection order, duplicate positions, and each resulting
  remainder list are preserved; element and remainder arguments may be
  constrained by term patterns.
- `nth0/3` or `nth1/3` over a ground proper list, optionally followed by
  arithmetic comparisons. The index may be a variable or integer, and the
  element may be constrained by a term pattern. Zero-based and one-based index
  results, list order, and duplicate elements are preserved.
- `between/3` with integer literal bounds and a variable or integer third
  argument, optionally followed by arithmetic comparisons. Ranges of at most
  10,000 values are converted; larger ranges are left unchanged. Reversed
  bounds convert to an empty result.
- `length/2` over a ground proper list with a variable or nonnegative integer
  length, optionally followed by arithmetic comparisons. A variable length
  yields the list's length; a mismatched integer length yields no result.

Supported comparisons are `>`, `>=`, `<`, `=<`, `=:=`, and `=\=`. Their
arithmetic expressions may use numeric constants, unary `+`, `-`, `abs`, and
binary `+`, `-`, `*`, `/`, `//`, `mod`, and `rem`. Filter variables must be
bound by the generator, and each successful template instance must be ground.
The converter interprets only this whitelisted arithmetic subset and does not
execute arbitrary filter goals.

The converter materializes the ordered template values that pass the filters
and replaces the goal with a call to a fresh, deterministic recursive list-copy
loop. It preserves source predicates and clause order. Unsupported generators,
recursive rule dependencies, rule bodies containing unsupported goals, other
built-ins, arbitrary filter predicates, unbound rule-body arithmetic, and
generators with variable-valued templates remain unchanged. `between/3` with
non-ground or non-integer bounds, or ranges above the limit, also remains
unchanged. `nth0/3` and `nth1/3` with a variable or improper list, or with an
index that is neither a variable nor an integer, remain unchanged.
`length/2` with a variable or improper list, or with a negative or non-integer
length, remains unchanged. `select/3` with a variable or improper list also
remains unchanged.

Rule bodies are interpreted only through this bounded pure subset; the
converter does not execute arbitrary rule goals. A dependency cycle, cut,
meta-call, or unsupported body goal prevents conversion. Each conversion report
cites the `findall_to_fold` lemma and records the generator-specific finiteness
condition (ground facts, finite acyclic rules, a ground list, or a bounded
`between/3` range), safe-arithmetic-filter condition, and deterministic-loop
condition. The report is an obligation, not itself a checked proof. The
independent proof checker validates conversions over predicates consisting
entirely of ground facts, including supported arithmetic-comparison filters, and
finite acyclic rule generators whose clauses use only ground facts, conjunction,
disjunction, `true`, `fail`, supported arithmetic comparisons, and calls to other
supported source predicates. It also checks ground-list `member/2` and
`select/3` with or without supported arithmetic-comparison filters,
`nth0/3`/`nth1/3` indices with supported filters, `length/2`, and bounded
`between/3`. For rule generators, clause and answer order and duplicate
derivations are preserved; recursive dependencies, unsupported body goals,
unsafe filters, arithmetic exceptions, and passing non-ground templates are
rejected. For a ground-fact generator, the checker preserves fact order and
duplicates and accepts bound or partially instantiated call arguments when
every successful template is ground. Arithmetic filters are limited to the
comparisons and expressions above and must be ground when reached. Conversions
involving unsupported built-in filters or other forms are not independently
checked. Do not treat such output as proof-certified.

Run the full suite, including loop2 tests, with:

```sh
swipl -q -s tests/run.pl
```

Run just the loop2 tests with:

```sh
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
```

# Detlog — conservative determinism analysis

`mnn_detlog:analyze_determinism/2` reports an initial, bounded analysis for each
predicate in an MNN program:

```prolog
detlog_report([
    predicate(Name/Arity, mode(all_arguments_unbound),
              determinism(Class), success_counts(Counts))
])
```

The analysis models counts `0`, `1`, and `2` (two or more) for a call with all
arguments unbound. It recognizes `true`, `fail`, conjunction, disjunction,
normalized if-then-else and negation, plus a whitelist of unification,
arithmetic-comparison, and type-test built-ins. Pairwise non-unifiable clause
heads are treated as exclusive. Calls to acyclic zero-arity predicates in the
same program are analyzed recursively, including their success counts; recursive
zero-arity calls are reported as unavailable. The reported classes are:

- `failure`: no successful derivations;
- `det`: exactly one successful derivation;
- `semidet`: zero or one;
- `multi`: one or more, with multiple derivations possible;
- `nondet`: failure or multiple derivations are possible.

Unsupported goals—including calls to predicates with arguments and cuts—are
returned as `unavailable(unsupported_goal(Goal))`; recursive zero-arity calls
are reported as `unavailable(recursive_call(Key))`. The analyzer does not guess
their determinism. This is a syntactic, conservative first slice, not general
mode or determinism inference. It does not execute goals, infer argument modes,
prove guard exhaustiveness, model effects, or account for bindings shared between
separate goals. In particular, do not use its report as a proof of equivalence.

Detlog code generation is not implemented: no choicepoint splicing, choice
packets, cut conversion, runtime constructs, or fallback diagnostics are emitted
yet. Red-cut safety proofs and source/output answer-sequence comparisons also
remain future work.

Run the focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"
```

Run the complete suite with `swipl -q -s tests/run.pl`.

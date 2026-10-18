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
normalized if-then-else and negation, `once/1`, plus a whitelist of unification,
arithmetic-comparison, and type-test built-ins. Ground goals in that whitelist are
evaluated to distinguish success from failure; raised exceptions are reported as
unavailable rather than treated as failure. It also classifies `between/3` when
both bounds are integer literals and the value is a variable or integer; variable
values receive a success count capped at two, while integer values are checked
against the inclusive range. `once(Goal)` preserves whether `Goal` may fail and
maps every positive success count to one, so a multi-success inner goal is
reported as at most one success. Unsupported inner goals remain unavailable.
Pairwise non-unifiable clause heads are treated as exclusive. Calls to acyclic
user predicates in the same program are analyzed recursively when every call
argument is a distinct unbound variable (zero-arity calls satisfy this condition).
Their success counts are propagated to the caller; recursive calls are reported
as unavailable.
Bound arguments and repeated variables in a call are unsupported. The reported
classes are:

- `failure`: no successful derivations;
- `det`: exactly one successful derivation;
- `semidet`: zero or one;
- `multi`: one or more, with multiple derivations possible;
- `nondet`: failure or multiple derivations are possible.

Unsupported goals—including calls with bound or repeated arguments and cuts—are
returned as `unavailable(unsupported_goal(Goal))`; recursive calls are reported
as `unavailable(recursive_call(Key))`. Exceptions from evaluated ground built-ins
are returned as `unavailable(exceptional_goal(Goal, Error))`. The analyzer does
not guess their determinism. This is a syntactic, conservative first slice, not
general mode or determinism inference. It does not infer argument modes, prove
guard exhaustiveness, model effects, or account for bindings shared between
separate goals. The bounded `between/3` case is a literal-range special case, not
general generator mode inference. In particular, do not use its report as a
proof of equivalence.

Detlog code generation is not implemented: no choicepoint splicing, choice
packets, cut conversion, runtime constructs, or fallback diagnostics are emitted
yet. Red-cut safety proofs and source/output answer-sequence comparisons also
remain future work.

Run the focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"
```

Run the complete suite with `swipl -q -s tests/run.pl`.

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
It also classifies the built-in `member/2` for a ground proper list with a
variable, ground, or partially instantiated element pattern. Each candidate is
matched against a copy of the pattern, so analysis does not bind variables in the
program and repeated variables within a pattern retain their sharing constraints.
Successes are counted up to two, so duplicate matching elements correctly make
the call multi; an empty list or a pattern with no matches fails. Variable lists,
improper or non-ground lists, and program-defined `member/2` predicates remain
unavailable.
The built-in `select/3` is classified for a ground proper list when the selected
value and remainder are each either unbound or ground. Counts are capped at two;
duplicate positions remain distinct successes, and ground value or remainder
patterns constrain the counted solutions. Variable or improper lists,
partially instantiated value or remainder patterns, and a program-defined
`select/3` remain unavailable.
The built-in `length/2` is also classified when its first argument is a ground
proper list and its length argument is unbound or a nonnegative integer. An
unbound length succeeds exactly once; a matching nonnegative integer succeeds
once and a mismatch fails. Variable or improper lists, negative or non-integer
length arguments, and a program-defined `length/2` are not handled by this
built-in case.
The built-ins `nth0/3` and `nth1/3` are classified for ground proper lists when
the index is an unbound variable or integer and the element is an unbound
variable or ground term. An unbound index and element must be distinct variables.
The analyzer counts matching positions up to two, so repeated elements can make
a ground-element query multi; a fixed index has at most one success. `nth0/3`
uses zero-based indices and `nth1/3` uses one-based indices. Improper or
non-ground lists, partially instantiated elements, shared unbound index/element
variables, and program-defined versions of these predicates remain unsupported.
The built-in `append/3` is classified as multi when all three arguments are
distinct unbound variables: it has at least two successful list splits, so the
reported count is capped at two. Repeated arguments and a program-defined
`append/3` are not treated as this built-in case. It is also classified as
deterministic or failing when all arguments are ground proper lists, or when
exactly one argument is unbound and the other two are ground proper lists. When
the first two arguments are distinct unbound variables and the third is a ground
proper list, the empty list has one split and is deterministic, while a nonempty
list has multiple splits and is classified as multi. The analyzer checks the
relation on copies of the arguments in the one-unbound mode; nonmatching lists
fail. Other calls with two or more unbound arguments, non-list or non-ground
inputs, and locally defined `append/3` remain unsupported.
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

The focused suite covers the supported `member/2` patterns, including partially
instantiated and repeated-variable patterns, duplicate matches, no matches, and
unsupported list shapes. It also covers `nth0/3` and `nth1/3`, including duplicate
values, out-of-range indices, and unsupported list or variable shapes. Run the
complete suite with `swipl -q -s tests/run.pl`. The append tests cover all
distinct-unbound, ground, one-unbound, and two-unbound modes, including empty and
nonempty ground lists and unsupported repeated or non-ground arguments.

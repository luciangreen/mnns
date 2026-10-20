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
the call multi; an empty list or a pattern with no matches fails. Improper or
non-ground lists and program-defined `member/2` predicates are unavailable for
this finite-list case. An unbound list with an element pattern independent of
that list is classified as multi: a matching element can occur at multiple
positions. A value/list alias such as `member(List, List)` remains unavailable.
The built-in `select/3` is classified for a ground proper list with arbitrary
selected-value and remainder patterns, including partially instantiated terms.
Each candidate value/remainder pair is matched against a copy of both patterns,
preserving sharing between them without binding the analyzed program. Counts are
capped at two; duplicate positions remain distinct successes. Variable or
improper lists and a program-defined `select/3` remain unavailable for this
finite-list case. When all three arguments
are distinct unbound variables, the call is classified as multi because the
built-in admits at least two list/value/remainder solutions. Repeated-variable
calls and program-defined `select/3` predicates are not treated as this mode.
For an unbound list, a ground selected value with an unbound remainder is
classified as multi. With a ground proper-list remainder and an unbound list,
the call has one success when the remainder is empty and multiple successes when
it is nonempty, whether the selected value is ground or an independent unbound
variable. A selected value aliased with the unbound list, partially instantiated
patterns, and locally defined `select/3` remain unavailable.
The built-in `length/2` is also classified when its first argument is a ground
proper list and its length argument is unbound or a nonnegative integer. An
unbound length succeeds exactly once; a matching nonnegative integer succeeds
once and a mismatch fails. Variable or improper lists, negative or non-integer
length arguments, and a program-defined `length/2` are not handled by this
built-in case. A variable list paired with a fixed nonnegative integer length is
also classified as deterministic: it has exactly one solution, including for
length zero. Distinct unbound list and length variables have multiple solutions,
so that mode is classified as multi; an aliased list and length variable remains
unsupported. Other non-ground list patterns and negative lengths remain
unavailable.
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
fail. It also classifies the two modes with an unbound output and one ground input
(`append(Prefix, GroundSuffix, List)` and
`append(GroundPrefix, Suffix, List)`) as multi: each has at least two possible
list results. Repeated-variable modes, other calls with two or more unbound
arguments, non-list or non-ground inputs, and locally defined `append/3` remain
unsupported.
Pairwise non-unifiable clause heads are treated as exclusive. Calls to acyclic
user predicates in the same program are analyzed recursively when every call
argument is a distinct unbound variable (zero-arity calls satisfy this condition).
Their success counts are propagated to the caller; recursive calls are reported
as unavailable. A ground-fact case also handles calls with partially instantiated argument
patterns, provided variables are not shared between distinct arguments. Each
candidate fact is unified with a fresh copy of the call, so nested patterns and
variable sharing within an argument are respected without binding the analyzed
program. Matching fact clauses count separately, including duplicate facts, and
the count is capped at two; unmatched calls fail. The predicate must consist
only of ground facts with `true` bodies. Calls with rules or non-ground fact
heads, and calls whose variables are shared between arguments, remain
unavailable. This narrow case does not extend analysis to general
bound-argument or repeated-variable modes, and the analyzer still does not track
bindings between separate goals. The reported classes are:

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

## Restricted `once/1` compilation

`mnn_detlog_transform:transform_program/3` provides an initial code-generation
slice. It lowers `once(Goal)` to `ite(Goal, true, fail)` when `Goal` contains
only `true`, `fail`, normalized conjunction, disjunction, if-then-else,
negation, and these pure built-ins: `=/2`, `\=/2`, `==/2`, `\==/2`, `is/2`,
arithmetic comparisons, the type tests `var/1`, `nonvar/1`, `atom/1`,
`atomic/1`, `compound/1`, `ground/1`, `integer/1`, `number/1`, and
`is_list/1`, plus built-in `member/2`, `between/3`, `append/3`, and `select/3`.
The compilation does not require these generators to be deterministic: the
if-then-else commits to their first condition solution, matching `once/1`, and
retains failure when the condition has no solution. A call is not compiled as a
built-in when the source program defines that predicate; it remains unchanged
instead. Restricting the condition to this side-effect-free subset avoids
changing effects or cut scope.

Unsupported `once/1` goals remain unchanged. The report is
`detlog_transform_report(Events)`, with `compiled_once(Predicate, ClauseId,
Goal)` and `kept_once(Predicate, ClauseId, unsupported_goal(Goal))` entries.
Other program fields, clause order, and source locations are preserved. This is
a bounded transformation report, not an independently checked proof.

This does not yet implement general mode inference, choicepoint splicing,
choice-packet generation, cut conversion, or fallback diagnostics. Red-cut
safety proofs and broader source/output answer-sequence checking remain future
work.

Run the focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"
swipl -q -g "load_files('tests/detlog_transform_tests.pl'), run_tests(mnn_detlog_transform), halt"
swipl -q -s tests/run.pl
```

The transformation tests include first-answer behavior for built-in `member/2`,
`between/3`, `append/3`, and `select/3`, failure preservation for `append/3` and
`select/3`, and checks that program-defined versions of these built-ins are not
treated as built-ins.

The focused suite covers ground-fact predicate calls with exact and
partially-instantiated patterns, including nested patterns, duplicate matches,
no matches, and unsupported shared variables across arguments. The supported
`member/2` patterns include partially
instantiated and repeated-variable patterns, duplicate matches, no matches,
unbound lists, and unsupported aliases and list shapes. It also covers `nth0/3`
and `nth1/3`, including duplicate values, out-of-range indices, and unsupported
list or variable shapes. Run the complete suite with `swipl -q -s tests/run.pl`.
The append tests cover all distinct-unbound, ground, one-unbound, and two-unbound
modes, including empty and nonempty ground lists and unsupported repeated or
non-ground arguments.
The `length/2` tests cover ground lists, variable lists with fixed nonnegative
lengths, and distinct unbound list and length variables, as well as unsupported
aliases, improper lists, negative lengths, and local definitions. Ground
user-call tests cover matching, missing and duplicate facts,
as well as rejection of non-fact definitions.
The `select/3` tests cover ground proper lists with unbound, ground, or partially
instantiated selected-value and remainder patterns, the distinct-unbound mode,
and unbound lists with ground selected values or proper-list remainders, including
duplicate positions, constrained results, aliases, and local definitions.
The Detlog transformation tests check compiled `once/1` answer preservation on
the supported pure subset and verify that cuts and user-predicate calls remain
unchanged.

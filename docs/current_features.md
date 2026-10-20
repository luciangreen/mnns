# Current features and tests

This guide describes the implemented subset, not the complete target suite in
[`PROGRAM_REQUIREMENTS.md`](../PROGRAM_REQUIREMENTS.md). The latter is the
specification for future work. [`PROGRESS.md`](../PROGRESS.md) tracks the current
stage-by-stage status.

## Feature and test map

The following are the implemented subsystems and their focused PlUnit suites.
Run commands from the repository root with SWI-Prolog 9.x or 10.x installed.
The focused suites help isolate failures; always run the full suite before
sharing a change.

| Feature | Implementation | Focused test command | Details |
| --- | --- | --- | --- |
| S2A input-address, integer-affine, quadratic, and cubic inference, plus example tables | `prolog/s2a/s2a.pl` | `swipl -q -g "load_files('tests/s2a_tests.pl'), run_tests(mnn_s2a), halt"` | [S2A synthesis](#s2a-synthesis) |
| Program IR, parser and emitter | `prolog/ir/ir.pl` | `swipl -q -g "load_files('tests/ir_tests.pl'), run_tests(mnn_ir), halt"` | [IR section](#program-ir) |
| Round-trip corpus | `tests/corpus/` | `swipl -q -g "load_files('tests/test_corpus.pl'), run_tests(mnn_ir_corpus), halt"` | [IR section](#program-ir) |
| Sandboxed execution | `prolog/runner/sandbox_runner.pl` | `swipl -q -g "load_files('tests/runner_tests.pl'), run_tests(mnn_sandbox_runner), halt"` | [Sandboxed execution](#sandboxed-execution) |
| Proof checker and renderer | `prolog/proof/` | `swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"` | [Proof checking](proof_rules.md); [Proof rendering](#proof-rendering) |
| PID analysis | `prolog/pid/pid.pl` | `swipl -q -g "load_files('tests/pid_tests.pl'), run_tests(mnn_pid), halt"` | [PID analysis](pid.md) |
| Tail recursion analysis | `prolog/pid/pid.pl` | `swipl -q -g "load_files('tests/pid_tests.pl'), run_tests(mnn_pid), halt"` | [PID analysis](pid.md) |
| Detlog determinism analysis | `prolog/detlog/detlog.pl` | `swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"` | [Detlog analysis](detlog.md) |
| Detlog `once/1` compilation | `prolog/detlog/detlog_transform.pl` | `swipl -q -g "load_files('tests/detlog_transform_tests.pl'), run_tests(mnn_detlog_transform), halt"` | [Detlog transformation](detlog.md#restricted-once-compilation) |
| loop2 conversion | `prolog/loop2/loop2.pl` | `swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"` | [loop2 conversion](loop2.md) |
| Proof-gated PLOp pipeline | `prolog/plop/plop.pl` | `swipl -q -g "load_files('tests/plop_tests.pl'), run_tests(mnn_plop), halt"` | [PLOp pipeline](#plop-pipeline) |
| AlgebraPLOp sequence analysis (initial) | `prolog/algebraplop/algebraplop.pl` | `swipl -q -g "load_files('tests/algebraplop_tests.pl'), run_tests(mnn_algebraplop), halt"` | [AlgebraPLOp](#algebraplop-sequence-inference) |
| AIOC structural size metric (initial) | `prolog/aioc/size.pl` | `swipl -q -g "load_files('tests/aioc_size_tests.pl'), run_tests(mnn_aioc_size), halt"` | [AIOC size metric](aioc.md) |
| Proof-checked MNN bundle writer and verifier (initial) | `prolog/aioc/bundle.pl` | `swipl -q -g "load_files('tests/bundle_tests.pl'), run_tests(mnn_aioc_bundle), halt"` | [MNN bundles](bundle.md) |

Run the complete suite, including every group above, with:

```sh
swipl -q -s tests/run.pl
```

This is also the command used by [CI](../.github/workflows/prolog-tests.yml).

## Program IR

`mnn_ir:parse_program/2` reads facts, rules, and directives into
`mnn_program(Name, Meta, Predicates, Proof, Trace)`. Each clause retains its
source order and source line; conjunction, disjunction, if-then(-else), and
negation are normalized in clause bodies, as are the goals inside `once/1`.
`mnn_ir:ir_to_prolog/2` emits terms in source order, and
`mnn_ir:emit_program/2` writes them to a file. Explicit `call/N` goals are
rejected rather than admitted as unrestricted meta-calls.

The round-trip corpus is grouped into recursive rules, control flow, lists and
generators, strings and terms, and built-ins and arithmetic. This verifies the
implemented source/emitter subset, not every feature of SWI-Prolog.

## Sandboxed execution

`mnn_sandbox_runner:run_program(File, Goal, Options, answers(Answers))` parses
the source, removes directives before loading clauses, checks the requested
goal using `library(sandbox)`, then runs it with a time limit and maximum answer
count. Options are `time_limit(Seconds)` and `max_answers(Count)`; defaults are
5 seconds and 100 answers. Only the requested query is executed, and unsafe or
unsupported goals are not run.

## Proof checking

`mnn_proof_checker:check_proof/4` checks supported proof terms directly against
the IR and does not import the optimizer. In addition to the rules described in
[`proof_rules.md`](proof_rules.md), it verifies `findall/3` conversions over
ground proper-list `member/2` generators when the template is ground for every
matching solution, including supported arithmetic-comparison filters on the
member generator, and `nth0/3` and `nth1/3` calls over ground proper lists. For
these index generators, the index may be variable or integer, the element may
use a constrained term pattern, and each passing template must be ground. The
checker independently reconstructs the generated values, helper, and complete
output IR. The `reorder_goals` rule additionally permits exactly one adjacent
swap when each goal
is either a supported ground unary type test or a ground whitelisted arithmetic
comparison that can be evaluated without arithmetic exceptions. Variable
comparisons and unsupported goals remain unavailable. The proof-checker focused
command below runs these cases alongside the other proof and renderer tests.
`nth0/3` and `nth1/3` also accept whitelisted arithmetic-comparison filters that
are ground after matching each index and element against the list. Indices remain
zero-based or one-based, respectively, and an empty ground list produces no
values. It also checks
`findall(Template, select(Value, GroundList, Rest), Results)` conversions with or
without supported arithmetic-comparison filters when each passing selected
solution grounds the template, preserving selection order and duplicate positions
while honoring value and remainder patterns. It also checks no-filter
conversions for `length/2` over a ground
proper list, with a variable or nonnegative integer length; a mismatch yields no
values. The `length/2` conversion also accepts whitelisted arithmetic-comparison
filters that become ground after matching the list length; arithmetic exceptions
are not certified. It checks bounded `between/3` conversions with integer bounds and a
variable or integer third argument when the inclusive range has at most 10,000
values; supported arithmetic-comparison filters may follow the generator.
Reversed bounds and nonmatching integer values yield no results.
It also verifies conversions over predicates made entirely of ground facts with
supported arithmetic-comparison filters, matching bound or partially
instantiated call arguments and preserving clause order and duplicate facts.
Filters must be ground after matching each fact; arithmetic exceptions are not
certified. For filtered member, select, and bounded `between/3` conversions,
comparisons must be ground after matching each value (and remainder for
`select/3`), and templates must be ground for every passing solution. Arithmetic
exceptions are not certified. These proof subsets exclude filters on built-in generators other than
`member/2`, `select/3`, `nth0/3`, `nth1/3`, `length/2`, and bounded `between/3`.
It also independently checks finite acyclic rule generators whose clauses are
ground facts or use only conjunction, disjunction, `true`, `fail`, supported
pure unification, arithmetic comparisons, other supported source-predicate
calls, and nested `findall/3` over supported finite built-in generators.
Unification operates on copied terms; conversions that would create cyclic terms
or encounter a source definition of `=/2` are declined. Nested built-ins must not
be shadowed; list generators require ground proper lists, and `between/3`
requires integer literal bounds. Nested templates must be ground for every
result. Unsupported goals, nested findall over source predicates, recursive
dependencies, non-ground passing templates, and arithmetic exceptions are
rejected. Oversized ranges and other list generators remain unsupported. The
renderer creates Markdown explanations but does not certify proofs. General
purity analysis, general clause/goal reordering, and most proof rules in the
requirements remain unsupported.

## Proof rendering

`mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown)` first calls
the independent proof checker and returns a Markdown report containing its
result. Accepted supported steps receive explanatory summaries; rejected or
unsupported proofs are displayed as quoted Prolog terms and marked with the
checker result. The report includes domain and mode annotations but does not
infer them. Identity, restricted goal reordering, definition introduction,
unfold, fold, and supported `findall_to_fold` steps can be rendered. Rendering
does not itself certify a proof; certification comes from the independent
checker. See [`proof_rules.md`](proof_rules.md) for supported proof rules and
their limitations.

Run the renderer tests with the proof-checker suite:

```sh
swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"
```

## PID analysis

`mnn_pid:analyze_program/2`, `analyze_measures/2`, and `analyze_induction/2`
provide call-graph classification, conservative measure checks, and schematic
clause obligations, respectively. Supported measures are shared structural
subterm decreases and guarded natural-number subtraction: `N > 0` for decrement
by one, or `N >= K` for subtraction by positive integer `K`. The guard must
precede the subtraction and recursive call so the measure remains nonnegative.
Mutual recursion is checked against one shared measure. Unsupported cases are
reported as unavailable. An induction report is not a termination proof or a
proof of a user specification. Recursive calls inside normalized `once/1` goals
are included in call-graph, measure, and induction analysis; tail-recursion
analysis conservatively marks them non-tail. `analyze_tail_recursion/2` also
classifies recursive calls by their syntactic tail position. See [`pid.md`](pid.md).

## Detlog analysis

`mnn_detlog:analyze_determinism/2` classifies success counts for a bounded set
of normalized goals in the all-arguments-unbound mode. It reports unsupported
goals rather than guessing; acyclic user-predicate calls within the program are
analyzed recursively when their arguments are distinct unbound variables, while
recursive calls and general bound-argument calls remain unavailable. Calls to
predicates defined exclusively by ground facts are counted up to two for exact
and partially instantiated patterns, including failure and duplicate matching
facts. Variables cannot be shared across distinct arguments in this pattern
mode; nested patterns and sharing within one argument are matched on copies.
Calls to rules, non-ground fact heads, or repeated variables across arguments
remain unsupported.
Ground goals from the whitelisted pure built-ins are evaluated exactly for
success or failure, while exceptions are reported as unavailable. Bounded
`between/3` calls with integer literal limits and a variable or integer value are
also classified, with success counts capped at two. Supported `once/1` goals
retain possible failure but cap every positive success count at one; unsupported
inner goals remain unavailable. The built-in `member/2` is classified for a
ground proper list with a variable, ground, or partially instantiated element
pattern. Each candidate is matched on a copy, preserving variable sharing without
binding the analyzed program; duplicate matches count as multiple successes.
Variable, improper, or non-ground lists and locally defined `member/2` predicates
are unsupported for this finite-list case. An unbound list with an independent
variable, ground, or structured element pattern is classified as multi because
matching elements can occur at multiple positions; an element pattern that
aliases the list is unsupported. Built-in `length/2` calls are classified for a
ground proper list and an unbound or nonnegative integer length: the unbound or
matching length succeeds once, and a mismatch fails. Variable/improper lists and
locally defined `length/2` predicates are not treated as this built-in case. A
variable list with a fixed nonnegative integer length is also classified as one
success; distinct unbound list and length variables are classified as multi.
Aliased variables remain unsupported. Built-in `select/3` is classified for
ground proper lists with unbound, ground, or partially instantiated selected-value
and remainder patterns; candidates are matched on copies that preserve sharing,
and duplicate positions count separately.
When all three arguments are distinct unbound variables, it is classified as
multi; aliases, other list/value shapes, and locally defined `select/3`
predicates remain unsupported by the built-in cases. With an unbound list and a
ground selected value plus unbound remainder, it is multi. With a ground
proper-list remainder and an unbound list, an empty remainder is deterministic
and a nonempty remainder is multi when the selected value is ground or an
independent variable.
Ground proper-list `nth0/3` and `nth1/3` calls are classified when the index is
variable or integer and the element is any term pattern. Matching is performed
on copies of the index and element together, preserving partially instantiated
or repeated-variable patterns and index/element sharing without binding the
analyzed program. Zero-/one-based indexing and duplicate matching elements are
accounted for; improper or non-ground lists and local definitions remain
unsupported.
Built-in `append/3` is classified as multi only when all three arguments are
distinct unbound variables; repeated-argument calls and locally defined
`append/3` predicates are not treated as the built-in. `append/3` is also
classified as deterministic or failing when all arguments are ground proper lists
or exactly one argument is unbound and the other two are ground proper lists.
With two distinct unbound arguments and a ground proper-list result, the empty
list has one split and is deterministic, while a nonempty list has multiple
splits and is classified as multi. The two modes with an unbound output and one
ground proper-list input are also classified as multi; other partially
instantiated append calls are unavailable. Choicepoint/cut conversion and general
mode inference are not implemented; see
[`detlog.md`](detlog.md).

### Restricted `once/1` compilation

`mnn_detlog_transform:transform_program/3` compiles `once(Goal)` to the IR
if-then-else form `ite(Goal, true, fail)` when `Goal` consists only of `true`,
`fail`, normalized conjunction, disjunction, if-then-else, negation, and the
pure unification, arithmetic-comparison, or type-test built-ins listed in
[`detlog.md`](detlog.md), plus built-in `member/2`, `between/3`, `length/2`,
`nth0/3`, `nth1/3`, `append/3`, and `select/3`. It compiles these calls only
when the source does not define the predicate. It leaves unsupported `once/1`
goals unchanged and reports each compiled or
retained occurrence as `compiled_once/3` or `kept_once/3`. Program metadata,
clause order, and source locations are retained. The resulting control
construct commits to the first success, matching `once/1` for this side-effect-
free subset. This report is not an independently checked proof, and the
transform also removes a redundant cut only when a predicate has one clause and
the complete body is `true, !` or one unification followed by `!`. The report
records `removed_green_cut/2`. Cuts after potentially nondeterministic goals,
inside multi-clause predicates, and in other positions are preserved. This
syntactic cut check is not independently proof-checked; general cut conversion,
red-cut safety proofs, mode inference, choicepoint splicing, and choice packets
remain unimplemented.

Run this focused suite from the repository root:

```sh
swipl -q -g "load_files('tests/detlog_transform_tests.pl'), run_tests(mnn_detlog_transform), halt"
```

The transformation tests include safe redundant-cut removal and regression
checks that nondeterministic and multi-clause cuts are preserved.

## S2A synthesis

`mnn_s2a:s2a/4` accepts a nonempty list of ground examples shaped as
`[[input, [['A', Input]]], [output, [['B', Output]]]]`. It first searches for a
unique input address whose subterm is identical to the output in every distinct
example. Addresses are lists of one-based compound-argument positions; `[]`
denotes the whole input. When it finds exactly one address across at least two
distinct examples, it emits one `Name/2` clause that preserves the constructors
along that address and shares the selected subterm with the output. Other
unselected input positions are variables, so the clause can handle held-out
values with the same structural path. For example, examples mapping
`box(red, [5,6])` to `[5,6]` and `box(blue, [7,8])` to `[7,8]` infer the
projection at address `[2]`.

If multiple addresses match, the default result is
`no_algorithm(ambiguous(Candidates))`; if none match, or there are fewer than two
distinct examples, the result is `no_algorithm(no_generalization_candidate)`.
When there is no matching input address and all examples have integer inputs and
outputs, S2A next attempts an exact integer-affine relation
`Output = Slope * Input + Intercept`. It requires at least two distinct input
values, integer coefficients, and exact agreement with every example. The
generated `Name/2` clause computes the output with `is/2`; examples such as
`1 -> 5`, `2 -> 7`, and `4 -> 11` infer `2 * Input + 3`. Fractional slopes,
non-integer examples, and inconsistent samples do not produce an affine
candidate. A unique input-address candidate takes precedence over affine
inference. With the explicit
option `[allow_table(true)]`, ambiguous or unsupported generalization cases may
instead produce a standalone module containing one `Name/2` fact per distinct
example. Repeated identical examples are emitted once, while conflicting outputs
for the same input, unsupported spec shapes, and invalid options return
`no_algorithm/1`.

If no affine relation fits, S2A tries an integer-quadratic relation
`Output = A * Input * Input + B * Input + C`. It requires at least three
distinct integer inputs, integer coefficients, and exact agreement with every
example. The generated clause evaluates the formula for held-out inputs;
fractional coefficients and inconsistent samples are rejected. Input-address
inference takes precedence over affine inference, which takes precedence over
quadratic inference, and then table fallback.

If no quadratic relation fits, S2A tries an integer-cubic relation
`Output = A * Input^3 + B * Input^2 + C * Input + D`. It requires at least four
distinct integer inputs, integer coefficients, and exact agreement with every
example. The generated clause evaluates the formula for held-out inputs;
fractional coefficients and inconsistent samples are rejected. Candidate
precedence is unique input-address projection, affine, quadratic, cubic, then
the opt-in table fallback.

The trace identifies the inferred address, affine, quadratic, or cubic formula,
or table, and counts examples reproduced. All modes currently use an empty
formal proof: address and integer-polynomial inference reproduce examples but do
not prove that the inferred relation is the intended function, and table mode
does not generalize to held-out inputs. S2A does not yet infer recursive list
algorithms such as reverse, broader arithmetic templates, or a formal
example-reproduction proof.

Run its focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/s2a_tests.pl'), run_tests(mnn_s2a), halt"
```

## loop2 conversion

`mnn_loop2:convert_program/3` currently handles a `findall/3` whose generator is
A direct call to a predicate made entirely of ground facts (including calls
with bound or partially instantiated arguments), a call through a finite acyclic
chain of supported facts and rules (also matching bound call arguments against
rule heads; these rules may contain a nested `findall/3` over a supported built-in
finite generator), or `member/2`, `select/3`, `append/3`, `nth0/3` or `nth1/3`
over a ground proper list, or `between/3` with integer literal bounds and a
variable or integer generator argument, or `length/2` over a ground proper list
with a variable or nonnegative integer length. Rule bodies
are limited to conjunction, disjunction, `true`, `fail`, supported source
predicate calls, and whitelisted arithmetic comparisons; recursive dependencies
and other goals are left unchanged. These generators may be followed by
arithmetic comparisons over values bound by the generator. Between ranges up to
10,000 values are supported, including reversed and singleton ranges; larger
ranges are left unchanged. Member, selection, append-split, and index-based generators preserve their
enumeration order and duplicate templates, including selection remainders and
the zero-based or one-based indices from `nth0/3` and `nth1/3`. `append/3`
enumerates prefixes in increasing length; its third argument must be a ground
proper list. The supported
comparisons are `>`, `>=`, `<`, `=<`, `=:=`, and `=\=`;
arithmetic expressions allow numeric constants, unary `+`, `-`, `abs`, and
binary `+`, `-`, `*`, `/`, `//`, `mod`, and `rem`. Ground templates are required
for each result that passes its filter. Arbitrary predicates in filters,
variable bounds or lists, unsupported rule bodies, other built-in generators,
and other forms are left unchanged. Conversion traverses supported findall goals
inside normalized conjunction, disjunction, if-then-else, negation, and `once/1`,
preserving those control structures.

Each conversion creates a uniquely named recursive list-copy predicate and
preserves the existing predicates and their clause order. The report records
finiteness and filter side conditions for the findall-to-fold lemma. The
independent proof checker validates ground-fact conversions, finite acyclic rule
generators with restricted pure bodies, including nested `findall/3` over supported
finite built-in generators, and the documented direct ground-list
`append/3`, `member/2`, `select/3`, `nth0/3`/`nth1/3` index, `length/2`, and bounded
`between/3` subsets. It supports whitelisted arithmetic filters on these rule
generators and on the built-in subsets documented in [`proof_rules.md`](proof_rules.md).
Nested findall over source predicates, unsupported filters, and other conversions
remain unchecked; do not treat them as proof-certified. See [`loop2.md`](loop2.md).

## PLOp pipeline

`mnn_plop:optimize_program/3` and `mnn_plop:optimize_predicate/4` share one
conservative pipeline. It calls the existing loop2 finite-generator conversion,
then submits the candidate and its sequential `findall_to_fold` proof steps to
the independent proof checker. A candidate is returned only when the checker
accepts the complete sequence.

The pipeline can apply multiple supported conversions in one run. It records each
conversion as a sequential proof step, and returns the transformed program only
when the independent checker accepts the complete sequence. The single-predicate
entry point likewise requires every change to be confined to the requested
predicate; it keeps the input unchanged if conversions would also modify another
predicate. Both entry points return `plop_report(Events, Proof, Status)`;
unchanged inputs include an identity proof, and accepted output includes the
checked rewrite proof. The pipeline does not infer costs and does not yet perform
unfold/fold search, memoization, common-subgoal hoisting, closed-form discovery,
or the other general PLOp rewrites. The accepted conversion subset and its
limitations are those documented for [loop2](loop2.md); output is proof-gated but
this initial pipeline does not claim to estimate or improve runtime cost.

Run PLOp tests with:

```sh
swipl -q -g "load_files('tests/plop_tests.pl'), run_tests(mnn_plop), halt"
```

## AlgebraPLOp sequence inference

`mnn_algebraplop:infer_sequence_formula/2` is an initial, conservative sequence
inference slice. It accepts a proper list of at least three integers, treats the
first value as position zero, and returns an exact constant, affine
`linear(Slope, Intercept)`, quadratic
`quadratic(Intercept, FirstDifference, SecondDifference)`, or higher-degree
`polynomial(NewtonCoefficients)` formula. It also detects integer-base geometric
sequences as `exponential(Initial, Base)`, representing `Initial * Base^Position`;
the first value must be nonzero so the base is uniquely determined. For a
polynomial, coefficient `k` is
the first value in the `k`th forward-difference row; at zero-based position `i`,
the result is the sum of `NewtonCoefficients[k] * binomial(i, k)`. For example,
`polynomial([1, 7, 12, 6])` describes the cubic sequence beginning
`1, 8, 27, 64, 125`.

The quadratic candidate is fitted from three samples and requires at least one
held-out sample. Geometric candidates are determined from the first two values
and require at least one held-out sample; the inferred integer base is then
checked against every remaining value. Higher-degree candidates are fitted from
degree-plus-one samples, require at least one held-out sample, and are tried in
ascending degree through at most `sample_count - 2`. Every supplied sample is verified.
Successful results use `verified_on(Samples)`; they are sample-verified, not
accompanied by a proof. Unsupported or inconsistent samples return `no_formula`.
The procedure is deterministic.

`mnn_algebraplop:invert_sequence_formula/3` inverts constant, affine, and
integer-base geometric and polynomial formulas. For a polynomial expressed in
Newton forward-difference coefficients, it returns `position(Index)` for one
exact nonnegative integer position or `positions(Indices)` for multiple finite
matches. It computes an exact Cauchy bound for the roots of the polynomial minus
the target, so an absent value is reported without unbounded searching. Constant
polynomials return `all_positions` when they match. The other result forms are
`all_positions` when every position matches and `positions(First, Step)` for an
infinite arithmetic progression of matching positions (`First + k*Step`, for
nonnegative integer `k`); the latter covers alternating values for base `-1`
and the zero tail for base `0`. Values outside the sequence, non-integer targets,
negative positions, and unsupported formulas return `no_position`. Inversion is
exact for the supplied formula but does not establish that the formula itself is
correct beyond its reported sample verification.

`mnn_algebraplop:evaluate_sequence_formula/3` evaluates any supported constant,
linear, quadratic, Newton-polynomial, or integer-base exponential formula at a
zero-based nonnegative integer position. It returns `value(Integer)` for a valid
formula and position, and `no_value` for unsupported formulas, malformed
coefficients, or invalid positions. This exact evaluation uses the formula as
given; `verified_on(Samples)` is metadata and is not independently rechecked.

Piecewise formulas, formulas from program index calculations, splice-index loops,
and `r_spec` provenance remain unsupported. The module also does not replace
program code. In particular,
`[2,4,8,16]` is reported as `exponential(2, 2)`, while prime samples return
`no_formula`.

Run this focused suite from the repository root:

```sh
swipl -q -g "load_files('tests/algebraplop_tests.pl'), run_tests(mnn_algebraplop), halt"
```

## Test commands

Run every test, including the corpus and all subsystem tests:

```sh
swipl -q -s tests/run.pl
```

Run an individual test group:

```sh
swipl -q -g "load_files('tests/ir_tests.pl'), run_tests(mnn_ir), halt"
swipl -q -g "load_files('tests/test_corpus.pl'), run_tests(mnn_ir_corpus), halt"
swipl -q -g "load_files('tests/runner_tests.pl'), run_tests(mnn_sandbox_runner), halt"
swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"
swipl -q -g "load_files('tests/pid_tests.pl'), run_tests(mnn_pid), halt"
swipl -q -g "load_files('tests/detlog_transform_tests.pl'), run_tests(mnn_detlog_transform), halt"
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"
swipl -q -g "load_files('tests/plop_tests.pl'), run_tests(mnn_plop), halt"
swipl -q -g "load_files('tests/algebraplop_tests.pl'), run_tests(mnn_algebraplop), halt"
swipl -q -g "load_files('tests/s2a_tests.pl'), run_tests(mnn_s2a), halt"
swipl -q -g "load_files('tests/aioc_size_tests.pl'), run_tests(mnn_aioc_size), halt"
swipl -q -g "load_files('tests/bundle_tests.pl'), run_tests(mnn_aioc_bundle), halt"
```

The single canonical full-suite command is also used in CI. Individual test
groups are for focused iteration and do not replace the full suite.

## Not yet implemented

The current work is an initial subset, not a completed version 1 suite:

- **Stages 1–5 are in progress.** Their implemented slices and limits are
  documented above and in the subsystem guides. In particular, Stage 4 still
  lacks independent checking of nested `findall/3` conversions and most other
  conversion proofs; the checker verifies ground-fact and finite acyclic rule generators
  with supported arithmetic filters, ground-list `member/2` and `select/3` with
  or without supported arithmetic filters, `nth0/3`/`nth1/3` with supported
  filter cases, `length/2` with or without supported arithmetic filters, and
  bounded `between/3` conversions with supported arithmetic filters. Stage 5
  adds only restricted compilation of pure `once/1` goals to the conservative
  success-count analysis; general mode inference, choicepoint splicing, choice
  packets, cut conversion, and fallback diagnostics are not implemented.
- **Stage 6 is in progress only for the proof-gated pipeline described above**;
  its full rewrite search and closed-form discovery remain unimplemented.
- **Stage 7 has an initial exact constant/affine/quadratic, higher-degree
  polynomial, and integer-base geometric sequence-inference slice**, with exact
  inverses for constant, affine, polynomial, and integer-base geometric formulas
  as described above; program-position extraction, splice-index loops,
  `r_spec` provenance, complexity ranking, and proof-backed formulas remain
  unimplemented.
- **Stage 8 has initial S2A input-address, integer-affine, integer-quadratic,
  and integer-cubic inference, plus an opt-in example-table fallback.** Recursive list
  generalization, broader arithmetic/list templates, formal example-reproduction
  proofs, and Starlog remain unimplemented.
- **Stage 9 is in progress:** the structural-size metric and proof-checked bundle
  writer/verifier are implemented. Incorporation front ends, simplification,
  candidate assessment, the library, and REPL commands remain.
- **Stages 10–14 are not started:** quantum-inspired search/export, AMNN/ANN/manual
  gradient descent, Neuroprolog, the MNN core/chatbot/agent, and benchmarks.

See [`PROGRESS.md`](../PROGRESS.md) for the complete stage table and the
acceptance work still outstanding for Stages 1–5. See
[`PROGRAM_REQUIREMENTS.md`](../PROGRAM_REQUIREMENTS.md) for the full version 1
specification.

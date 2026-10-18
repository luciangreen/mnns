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
| Program IR, parser and emitter | `prolog/ir/ir.pl` | `swipl -q -g "load_files('tests/ir_tests.pl'), run_tests(mnn_ir), halt"` | [IR section](#program-ir) |
| Round-trip corpus | `tests/corpus/` | `swipl -q -g "load_files('tests/test_corpus.pl'), run_tests(mnn_ir_corpus), halt"` | [IR section](#program-ir) |
| Sandboxed execution | `prolog/runner/sandbox_runner.pl` | `swipl -q -g "load_files('tests/runner_tests.pl'), run_tests(mnn_sandbox_runner), halt"` | [Sandboxed execution](#sandboxed-execution) |
| Proof checker and renderer | `prolog/proof/` | `swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"` | [Proof checking](proof_rules.md) |
| PID analysis | `prolog/pid/pid.pl` | `swipl -q -g "load_files('tests/pid_tests.pl'), run_tests(mnn_pid), halt"` | [PID analysis](pid.md) |
| Detlog determinism analysis | `prolog/detlog/detlog.pl` | `swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"` | [Detlog analysis](detlog.md) |
| loop2 conversion | `prolog/loop2/loop2.pl` | `swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"` | [loop2 conversion](loop2.md) |

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
the IR and does not import the optimizer. Supported steps and their restrictions
are detailed in [`proof_rules.md`](proof_rules.md). The renderer creates
Markdown explanations but does not certify proofs. General purity analysis,
general clause/goal reordering, and most proof rules in the requirements remain
unsupported.

## PID analysis

`mnn_pid:analyze_program/2`, `analyze_measures/2`, and `analyze_induction/2`
provide call-graph classification, conservative measure checks, and schematic
clause obligations, respectively. Supported measures are shared structural
subterm decreases and a guarded natural-number subtraction pattern. Mutual
recursion is checked against one shared measure. Unsupported cases are reported
as unavailable. An induction report is not a termination proof or a proof of a
user specification. `analyze_tail_recursion/2` also classifies recursive calls
by their syntactic tail position. See [`pid.md`](pid.md).

## Detlog analysis

`mnn_detlog:analyze_determinism/2` classifies success counts for a bounded set
of normalized goals in the all-arguments-unbound mode. It reports unsupported
goals rather than guessing; acyclic user-predicate calls within the program are
analyzed recursively when their arguments are distinct unbound variables, while
recursive, bound-argument, and repeated-argument calls remain unavailable.
Bounded `between/3` calls with integer literal limits and a variable or integer
value are also classified, with success counts capped at two. Supported `once/1`
goals retain possible failure but cap every positive success count at one;
unsupported inner goals remain unavailable.
Choicepoint/cut conversion and general mode inference are not implemented; see
[`detlog.md`](detlog.md).

## loop2 conversion

`mnn_loop2:convert_program/3` currently handles a `findall/3` whose generator is
A direct call to a predicate made entirely of ground facts (including calls
with bound or partially instantiated arguments), a call through a finite acyclic
chain of supported facts and rules (also matching bound call arguments against
rule heads), or `member/2`, `select/3`, `nth0/3` or `nth1/3` over a ground proper
list, or `between/3` with integer literal bounds and a variable
or integer generator argument, or `length/2` over a ground proper list with a
variable or nonnegative integer length. Rule bodies
are limited to conjunction, disjunction, `true`, `fail`, supported source
predicate calls, and whitelisted arithmetic comparisons; recursive dependencies
and other goals are left unchanged. These generators may be followed by
arithmetic comparisons over values bound by the generator. Between ranges up to
10,000 values are supported, including reversed and singleton ranges; larger
ranges are left unchanged. Member, selection, and index-based generators
preserve list order and duplicates, including selection remainders and the
zero-based or one-based indices from `nth0/3` and `nth1/3`. The supported
comparisons are `>`, `>=`, `<`, `=<`, `=:=`, and `=\=`;
arithmetic expressions allow numeric constants, unary `+`, `-`, `abs`, and
binary `+`, `-`, `*`, `/`, `//`, `mod`, and `rem`. Ground templates are required
for each result that passes its filter. Arbitrary predicates in filters,
variable bounds or lists, unsupported rule bodies, other built-in generators,
and other forms are left unchanged.

Each conversion creates a uniquely named recursive list-copy predicate and
preserves the existing predicates and their clause order. The report records
finiteness and filter side conditions for the findall-to-fold lemma, but the
independent proof checker does not yet validate this conversion. Do not treat
the output as proof-certified; see [`loop2.md`](loop2.md).

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
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"
```

The single canonical full-suite command is also used in CI. Individual test
groups are for focused iteration and do not replace the full suite.

## Not yet implemented

The current work is an initial subset, not a completed version 1 suite:

- **Stages 1–5 are in progress.** Their implemented slices and limits are
  documented above and in the subsystem guides. In particular, Stage 4 still
  lacks nested `findall/3` conversion and independent checking of conversion
  proofs. Stage 5 has only conservative success-count analysis; mode inference,
  Detlog code generation, and choicepoint/cut transformations are not
  implemented.
- **Stages 6–14 are not started:** PLOp, AlgebraPLOp, S2A/Starlog, the AIOC
  pipeline and bundle interface, quantum-inspired search/export, AMNN/ANN/manual
  gradient descent, Neuroprolog, the MNN core/chatbot/agent, and benchmarks.

See [`PROGRESS.md`](../PROGRESS.md) for the complete stage table and the
acceptance work still outstanding for Stages 1–5. See
[`PROGRAM_REQUIREMENTS.md`](../PROGRAM_REQUIREMENTS.md) for the full version 1
specification.

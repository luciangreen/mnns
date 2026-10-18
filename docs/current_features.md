# Current features and tests

This guide describes the implemented subset, not the complete target suite in
[`PROGRAM_REQUIREMENTS.md`](../PROGRAM_REQUIREMENTS.md). The latter is the
specification for future work. [`PROGRESS.md`](../PROGRESS.md) tracks the current
stage-by-stage status.

## Program IR

`mnn_ir:parse_program/2` reads facts, rules, and directives into
`mnn_program(Name, Meta, Predicates, Proof, Trace)`. Each clause retains its
source order and source line; conjunction, disjunction, if-then(-else), and
negation are normalized in clause bodies. `mnn_ir:ir_to_prolog/2` emits terms
in source order, and `mnn_ir:emit_program/2` writes them to a file. Explicit
`call/N` goals are rejected rather than admitted as unrestricted meta-calls.

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
user specification; see [`pid.md`](pid.md).

## loop2 conversion

`mnn_loop2:convert_program/3` currently handles a `findall/3` whose generator is
a direct call to a predicate made entirely of ground facts, or `member/2` over a
ground proper list. Either may be followed by arithmetic comparisons over values
bound by the generator. It also converts `between/3` with integer literal bounds
and a variable or integer generator argument, optionally followed by the same
arithmetic comparisons. Between ranges up to 10,000 values are supported,
including reversed and singleton ranges; larger ranges are left unchanged.
Member list order and duplicates are preserved. The supported comparisons are
`>`, `>=`, `<`, `=<`, `=:=`, and `=\=`; arithmetic expressions allow numeric
constants, unary `+`, `-`, `abs`, and binary `+`, `-`, `*`, `/`, `//`, `mod`, and
`rem`. Ground templates are required for each result that passes its filter.
Filter expressions are interpreted through this restricted arithmetic
whitelist; arbitrary predicates, unbound arithmetic, variable bounds or lists,
rules, other built-in generators, and other forms are left unchanged.

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
```

The single canonical full-suite command is also used in CI. Individual test
groups are for focused iteration and do not replace the full suite.

## Not yet implemented

Stages 5–14 remain unstarted: Detlog, PLOp, AlgebraPLOp, S2A/Starlog, the AIOC
pipeline and bundle interface, quantum-inspired search/export, AMNN/ANN/manual
gradient descent, Neuroprolog, core/chatbot/agent, and benchmarks. Stages 1–4
are also incomplete; consult `PROGRESS.md` for their limitations and next
acceptance criteria. In Stage 4, `nth0/3`, `nth1/3`, rule-based generators,
nested `findall/3`, and independent proof checking for conversions remain.

# MNN Suite implementation status

Implementation follows the stages in `PROGRAM_REQUIREMENTS.md` (§16). A stage is
marked complete only when its listed deliverables and acceptance criteria pass.

## Current work

- **Stage 1 — IR, parser, emitter, sandboxed runner, test harness, CI: in progress.**
  The initial parser/emitter slice is in place for ordinary clauses, facts,
  directives and normalized conjunction, disjunction, if-then(-else) and
  negation. Source locations and source order are retained, and explicit `call/N`
  goals are rejected. The sandboxed runner strips source directives before loading clauses,
  validates queries with SWI-Prolog's sandbox, and bounds time and answer count.
  A round-trip corpus now covers recursive rules, cuts, control flow, generators,
  lists, arithmetic, strings, terms, and required list/generator built-ins,
  including `nth0/3`, `nth1/3`, and `between/3` round trips. The runner has
  execution checks for list operations, arithmetic, finite-generator boundaries,
  cut-based control flow, negation, recursion, both list-indexing predicates,
  strings, atoms and nested terms. CI runs the Prolog test suite on pushes and
  pull requests. Stage 1 remains in progress: full supported-syntax acceptance
  coverage and successful CI validation are still outstanding.
- Current validation command: `swipl -q -s tests/run.pl` (the new CI job runs this
  command).
- **Stage 2 — proof system: in progress.** The independent checker accepts
  identity proofs, narrowly scoped `reorder_goals` rewrites (swapping one
  adjacent pair of ground, pure unary type tests per step), and one-occurrence
  `introduce_definition` rewrites that factor one ground pure goal into a fresh
  zero-arity helper or a one-variable pure goal into a fresh unary helper.
  One-occurrence `unfold` and `fold` rewrites support matching
  single-clause ground definitions and unary variable definitions whose bodies
  use only the listed pure type tests, `true`, `fail`, conjunction and
  disjunction; variable-bearing folds require variant body matching to preserve
  variable sharing. Ordered sequences of these checked steps can be
  independently verified and rendered as Markdown reports. General
  purity/determinism analysis, general goal/clause reordering, and the other
  proof rules remain unsupported.
- **Stage 3 — PID: in progress.** The call-graph analysis classifies predicates
  as recursive or non-recursive, including mutual recursion and non-recursive
  wrappers. The separate measure analysis identifies a structural measure when
  every recursive call in a strongly connected component passes a strict
  subterm at the same argument position (including nested compound subterms);
  it reports per-call decrease obligations. It also recognizes a narrow
  guarded natural-number decrease pattern with an integer type test, a positive
  guard, and a direct subtraction before each recursive call, including across
  mutual-recursion components when every call decreases the same argument.
  `analyze_induction/2` now emits symbolic clause obligations for predicates
  with these verified measures, listing induction hypotheses for each recursive
  call (including mutual recursion). Other arithmetic measures and unsupported
  forms are explicitly reported as unavailable. The templates do not verify
  full termination or user specifications, and user-declared measures remain
  unsupported. A syntactic tail-recursion report now identifies tail calls and
  lists recursive calls that are followed by more work.
- **Stage 4 — loop2: in progress.** `mnn_loop2:convert_program/3` converts
  `findall/3` over a predicate consisting only of ground facts, including calls
  with bound or partially instantiated arguments, or `member/2`, `nth0/3`, and
  `nth1/3` over ground proper lists, when each matching template instance is
  ground. List order, duplicate answers, and zero-based or one-based indices are
  preserved. It also handles `between/3` with integer literal bounds and a
  variable or integer third argument, optionally followed by whitelisted
  arithmetic comparisons; ranges are limited to 10,000 values and reversed
  bounds produce an empty result. The supported comparisons and arithmetic
  operators are listed in `docs/loop2.md`. Finite acyclic rule generators are
  supported when their bodies contain only conjunction, disjunction, `true`,
  `fail`, supported source calls, and bound whitelisted arithmetic comparisons;
  bound call arguments are matched against rule heads. Arbitrary predicate
  filters, variable bounds, recursive dependencies, unsupported rule bodies,
  nested `findall/3`, and independent checking of conversion proofs remain
  unsupported. The converter
  emits a distinct deterministic recursive list-copy helper for each conversion.
  Its report cites the findall-to-fold lemma and
  records finiteness, safe-filter, and determinism side conditions as an
  obligation; independent proof-checker support for this rule is not yet
  implemented.

## Remaining stages

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | IR, parser, emitter, sandboxed runner, test harness, CI | In progress |
| 2 | Proof term format, independent checker, rewrite rules, rendering | In progress (identity, restricted ground-test reordering, ground or unary-variable definition introduction, and narrow ground or unary variable type-test unfold/fold) |
| 3 | PID termination measures and induction obligations | In progress (call-graph classification, shared structural subterm and guarded natural-number measures for mutual recursion, schematic measure-backed clause obligations, and syntactic tail-recursion classification; user specifications, broader measure forms, and full termination proofs remain) |
| 4 | loop2 finite-generator loop conversions | In progress (ground facts, finite acyclic rule chains, ground proper-list `member/2`, `nth0/3`, `nth1/3`, and bounded ground `between/3` ranges with restricted arithmetic filters; nested findall and checked conversion proofs remain) |
| 5 | Detlog determinism analysis and transformations | In progress (conservative count analysis for a limited set of normalized goals in the all-arguments-unbound mode, including acyclic zero-arity calls; general mode inference, argument-bearing calls, choicepoint/cut transformations, runtime constructs, and fallback diagnostics remain) |
| 6 | PLOp optimization pipeline and proved closed forms | Not started |
| 7 | AlgebraPLOp positional algebra | Not started |
| 8 | S2A synthesis and Starlog view | Not started |
| 9 | AIOC incorporation, simplification, assessment, bundles, library, REPL | Not started |
| 10 | Quantum-inspired search/export, allocation and cycle interaction | Not started |
| 11 | AMNN, ANN and manual gradient descent | Not started |
| 12 | Neuroprolog mode | Not started |
| 13 | MNN core, chatbot and sandboxed agent | Not started |
| 14 | Benchmarks and evaluation report | Not started |

The requirements in §§1–15 and the version 1 definition of done in §17 remain
the specification; this table is a status summary, not a reduction in scope.

The Detlog slice is described in `docs/detlog.md`; its tests are included in the
full test runner and can also be run with
`swipl -q -g "load_files('tests/detlog_tests.pl'), run_tests(mnn_detlog), halt"`.
See `docs/current_features.md` for the implemented feature descriptions,
limitations, and focused test commands. Run the full current test suite with
`swipl -q -s tests/run.pl`.

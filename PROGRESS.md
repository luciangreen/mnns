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
  zero-arity helper, plus one-occurrence `unfold` and `fold` rewrites for
  matching single-clause definitions with ground heads and bodies made only of
  pure built-ins, `true`, `fail`, conjunction and disjunction. Ordered sequences
  of these checked steps can be independently verified and rendered as Markdown
  reports. General purity/determinism analysis, general goal/clause reordering,
  and the other proof rules remain unsupported.
- **Stage 3 — PID: in progress.** The call-graph analysis classifies predicates
  as recursive or non-recursive, including mutual recursion and non-recursive
  wrappers. The separate measure analysis identifies a structural measure when
  every direct self-recursive call passes a strict subterm of the same compound
  argument (including nested compound subterms); it reports per-call decrease
  obligations. It also recognizes a narrow natural-number decrease pattern
  with an integer type test, a positive guard, and a direct subtraction before
  each recursive call. Mutual recursion, other arithmetic measures and other
  unsupported forms are explicitly reported as unavailable. It does not yet
  verify full termination, generate induction proofs, or check user
  specifications.

## Remaining stages

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | IR, parser, emitter, sandboxed runner, test harness, CI | In progress |
| 2 | Proof term format, independent checker, rewrite rules, rendering | In progress (identity, restricted ground-test reordering, ground definition introduction, and narrow ground unfold/fold only) |
| 3 | PID termination measures and induction obligations | In progress (call-graph classification, strict structural subterm measures, and a guarded natural-number decrement subset; induction proofs and broader measure forms remain) |
| 4 | loop2 finite-generator loop conversions | Not started |
| 5 | Detlog determinism analysis and transformations | Not started |
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

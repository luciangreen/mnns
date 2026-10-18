# MNN Suite implementation status

Implementation follows the stages in `PROGRAM_REQUIREMENTS.md` (§16). A stage is
marked complete only when its listed deliverables and acceptance criteria pass.

## Current work

- **Stage 1 — IR, parser, emitter, sandboxed runner, test harness, CI: in progress.**
  The initial parser/emitter slice is in place for ordinary clauses, facts,
  directives and normalized conjunction, disjunction, if-then(-else) and
  negation. Source locations and source order are retained, and `call/1` is
  rejected. The sandboxed runner strips source directives before loading clauses,
  validates queries with SWI-Prolog's sandbox, and bounds time and answer count.
  A round-trip corpus now covers recursive rules, cuts, control flow, generators,
  lists, arithmetic, strings and terms. Stage 1 is not complete: CI, full
  supported syntax coverage and the complete acceptance corpus remain to be
  implemented and validated. The runner has only been tested against its focused
  tests; SWI-Prolog is unavailable in the current environment.
- Current validation command: `swipl -q -s tests/run.pl` (not run in this
  environment because SWI-Prolog is unavailable).

## Remaining stages

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | IR, parser, emitter, sandboxed runner, test harness, CI | In progress |
| 2 | Proof term format, independent checker, rewrite rules, rendering | Not started |
| 3 | PID termination measures and induction obligations | Not started |
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

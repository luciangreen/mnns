# MNN Suite implementation status

Implementation follows the stages in `PROGRAM_REQUIREMENTS.md` (§16). A stage is
marked complete only when its listed deliverables and acceptance criteria pass.

## Current work

- **Stage 1 — IR, parser, emitter, sandboxed runner, test harness, CI: in progress.**
  The initial parser/emitter slice is in place for ordinary clauses, facts,
  directives and normalized conjunction, disjunction, if-then(-else), negation,
  and bodies inside `once/1`. Source locations and source order are retained, and
  explicit `call/N` goals are rejected. The sandboxed runner strips source
  directives before loading clauses,
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
  variable sharing. It also independently checks ground-list
  `findall(Value, member(Value, GroundList), Results)` conversions, with supported
  arithmetic-comparison filters, and conversions for
  `findall(Index, nth0(Index, GroundList, _), Results)` and
  `findall(Index, nth1(Index, GroundList, _), Results)`, including supported
  arithmetic-comparison filters when the index and element are distinct
  unbound variables, plus `findall(Template, select(Value, GroundList, Rest),
  Results)` with or without supported arithmetic-comparison filters when each
  passing selected template is ground, and `findall(Length, length(GroundList,
  Length), Results)` for variable or nonnegative integer lengths. It also checks bounded
  `between/3` conversions with integer bounds and a variable or integer value,
  for ranges up to 10,000, including supported arithmetic-comparison filters,
  and calls to predicates whose clauses are all ground facts with supported
  arithmetic-comparison filters. Fact order,
  duplicate facts, and bound or
  partially instantiated call patterns are checked by rebuilding the output;
  every matching template must be ground. Selection order, duplicate positions,
  and value/remainder patterns are checked by rebuilding
  the expected output and deterministic copy helper. Ordered sequences of
  these checked steps can be independently verified and rendered as Markdown
  reports. Filters on ground-fact generators are checked only for whitelisted
  arithmetic comparisons with ground operands. The checker also validates
  supported arithmetic-comparison filters on ground-list `member/2`, `select/3`,
  `nth0/3`, and `nth1/3` conversions, plus
  supported arithmetic filters on bounded integer-literal `between/3`.
  Rule generators, filters on the other built-in generators, other findall
  conversions, general purity/determinism analysis, general goal/clause
  reordering, and the other proof rules remain unsupported.
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
  with bound or partially instantiated arguments; `member/2`, `select/3`,
  `nth0/3`, and `nth1/3` over ground proper lists; and `length/2` over a ground
  proper list with a variable or nonnegative integer length. Each matching
  template instance must be ground. List order, duplicate answers, indices, and
  selection remainders are preserved. It also handles `between/3` with integer
  literal bounds and a
  variable or integer third argument, optionally followed by whitelisted
  arithmetic comparisons; ranges are limited to 10,000 values and reversed
  bounds produce an empty result. The supported comparisons and arithmetic
  operators are listed in `docs/loop2.md`. Finite acyclic rule generators are
  supported when their bodies contain only conjunction, disjunction, `true`,
  `fail`, supported source calls, and bound whitelisted arithmetic comparisons;
  bound call arguments are matched against rule heads. Arbitrary predicate
  filters, variable bounds, recursive dependencies, unsupported rule bodies,
  and nested `findall/3` remain unsupported. Most conversion proofs are not
  independently checked; the proof checker validates ground-fact generators
  with supported arithmetic-comparison filters and ground-list `member/2`,
  `select/3`, `nth0/3`, and `nth1/3` subsets with supported arithmetic filters,
  plus direct no-filter `nth0/3`/`nth1/3` index and `length/2` subsets and bounded
  integer-literal `between/3` with supported arithmetic filters.
  Conversion traverses supported `findall/3` goals inside normalized
  conjunction, disjunction, if-then-else, negation, and `once/1`, preserving the
  surrounding control structure. The converter emits a distinct deterministic
  recursive list-copy helper for each conversion.
  Its report cites the findall-to-fold lemma and records finiteness, safe-filter,
  and determinism side conditions as an obligation; the independent checker
  validates the documented ground-fact, ground-list, and bounded `between/3`
  subsets.

## Remaining stages

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | IR, parser, emitter, sandboxed runner, test harness, CI | In progress |
| 2 | Proof term format, independent checker, rewrite rules, rendering | In progress (identity, restricted ground-test reordering, ground or unary-variable definition introduction, narrow type-test unfold/fold, ground-fact generators and ground-list member/select/nth0/nth1 conversions with supported arithmetic filters, no-filter nth0-index/nth1-index/length conversions, and bounded integer-literal between conversions with supported arithmetic filters) |
| 3 | PID termination measures and induction obligations | In progress (call-graph classification, shared structural subterm and guarded natural-number measures for mutual recursion, schematic measure-backed clause obligations, and syntactic tail-recursion classification; user specifications, broader measure forms, and full termination proofs remain) |
| 4 | loop2 finite-generator loop conversions | In progress (ground facts, finite acyclic rule chains, ground proper-list `member/2`, `select/3`, `nth0/3`, `nth1/3`, `length/2`, and bounded ground `between/3` ranges with restricted arithmetic filters; independent proof checks include filters on member/select/nth0/nth1/bounded between; nested findall and general checked conversion proofs remain) |
| 5 | Detlog determinism analysis and transformations | In progress (conservative count analysis for a limited set of normalized goals in the all-arguments-unbound mode, including acyclic calls with distinct unbound arguments, ground whitelisted built-ins with exceptions reported unavailable, bounded literal `between/3`, `member/2` over supported ground proper lists with variable, ground, or partially instantiated element patterns, `select/3` over supported ground proper lists, `nth0/3` and `nth1/3` over ground proper lists with variable/integer indices and variable/ground elements, `length/2`, `append/3` with three distinct unbound arguments, all ground proper-list arguments, or exactly one unbound argument and two ground proper lists, and `once/1` count capping; general mode inference, most bound/repeated-argument calls, choicepoint/cut transformations, runtime constructs, and fallback diagnostics remain) |
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

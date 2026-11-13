# Manual Neuronets

MNN Suite is an in-progress SWI-Prolog implementation of proof-carrying
optimisations for Prolog algorithms. It represents programs in a shared
intermediate representation (IR), runs them in a bounded sandbox, and includes
early implementations of an independent proof checker, termination analysis,
and finite-generator loop conversion.

This repository implements only a subset of the full vision in
[`PROGRAM_REQUIREMENTS.md`](PROGRAM_REQUIREMENTS.md). It includes initial Detlog
analysis and a restricted pure `once/1` compilation slice, but not general
Detlog transformations. S2A supports a conservative unique input-address
projection, integer polynomial relations through degree three, and explicitly
opted-in example tables; Starlog currently has an initial function-expression
view. AIOC has initial proof-checked decision-tree and grammar incorporation,
simplification, assessment, deterministic budget allocation, bundles, and
library features. The allocation planner is connected to proof-gated candidate
search and a bounded iterative controller that stops at a structural fixed
point or cycle limit; it does not dispatch work or enforce resource budgets.
Recursive generalization, the end-user MNN compiler, general PLOp optimization,
the complete AIOC controller, neural-network, chatbot, and agent features remain
incomplete.
A proof-gated
PLOp pipeline currently exposes a limited set of independently checked
finite-generator conversions. See [`PROGRESS.md`](PROGRESS.md) for the
stage-by-stage implementation status and remaining work.

New to the project? Start with the [quick-start guide](docs/quick_start.md) for
installation, runnable parser and sandbox examples, and test commands. The
[current feature guide](docs/current_features.md) documents every implemented
feature and its focused test suite.

## Implemented features

- **IR parser and emitter:** reads Prolog clauses and directives into
  `mnn_program/5`, preserves clause order and source locations, normalizes
  control-flow goals and `once/1` bodies, and emits Prolog. Explicit `call/N`
  goals are rejected.
- **Sandboxed runner:** strips source directives, checks requested goals with
  SWI-Prolog's sandbox, and limits execution time and answer count. See
  [`prolog/runner/sandbox_runner.pl`](prolog/runner/sandbox_runner.pl).
- **Proof checker and renderer:** independently checks identity, one adjacent
  reordering of restricted ground type tests, safe ground arithmetic comparisons
  or `is/2` assignments, restricted definition
  introduction, narrow single-occurrence unfold/fold steps, and `findall/3`
  conversions over ground facts, `member/2`, `select/3`, `nth0/3`, and `nth1/3`,
  with supported arithmetic-comparison filters. Ground-list `member/2` checks
  allow constrained values and any template that is ground for every matching
  solution. It also checks filtered and
  no-filter conversions over `length/2`, plus bounded `between/3` conversions with or
  without supported arithmetic-comparison filters, and finite acyclic rule
  generators with restricted pure bodies, including nested `findall/3` over
  supported finite built-in generators. For `nth0/3` and `nth1/3`, the index may
  be variable or integer and the element may be constrained by a term pattern;
  each passing template must be ground. Selection order, fact order, and duplicate
  answers are preserved; indices are checked
  as zero-based for `nth0/3` and one-based for `nth1/3`. Unsupported proof rules and
  broader findall conversions are rejected.
  See [`docs/proof_rules.md`](docs/proof_rules.md).
- **PID analysis:** classifies recursive predicates, checks a limited set of
  shared structural and guarded natural-number decreases, and emits schematic
  induction obligations for supported measures, including recursive calls inside
  normalized `once/1`; it also identifies syntactic tail recursion and treats
  calls inside `once/1` as non-tail. These analyses are not proofs of a
  specification or full termination. See [`docs/pid.md`](docs/pid.md).
- **Detlog2, PLOp2 and AlgebraPLOp2 (separate repositories):** the full Detlog is now
  [detlog2](https://github.com/luciangreen/detlog2), per-character PLOp is
  [plop2](https://github.com/luciangreen/plop2), and proof-backed AlgebraPLOp is
  [algebraplop2](https://github.com/luciangreen/algebraplop2). All are written in Haskell and
  carry checked proofs for every rewrite.
  - detlog2 is a choicepointless, cutless interpreter. Its converter turns cuts
    into `if_commit/3` and choicepoints into `splice/2`/`member_cp/2` packets,
    and it memoises calls into answer tables.
  - plop2 writes one separate, demand-sliced program per output character, with
    closed forms from this repository's AlgebraPLOp.
  - algebraplop2 proves program-position formulas by induction (or verifies
    them on a domain), and writes inverses and splice-index loops.
  - detlog2 and plop2 run this repository's `optimise.pl` and AlgebraPLOp as
    their mnns pass; algebraplop2 compares its formulas with this AlgebraPLOp.
  - The Detlog and PLOp slices below remain here because `optimise.pl` uses them.
- **Detlog analysis:** conservatively classifies success counts for a limited
  set of normalized goals when all predicate arguments are unbound. Unsupported
  goals are reported rather than guessed; acyclic user-predicate calls with
  distinct unbound arguments are analyzed recursively, ground whitelisted
  built-ins are evaluated for success or failure, and calls to predicates
  consisting only of ground facts count exact and partially instantiated
  patterns up to two successes when variables are not shared across arguments.
  Bounded literal `between/3`
  calls are classified, and `once/1` caps reported successes at one. General
  choicepoint transformation and operational cut conversion are not implemented;
  Detlog removes a cut after a deterministic built-in guard in a singleton
  clause, and lowers a terminal cut after a supported guard in a singleton
  clause to committed if-then-else IR; cuts in multi-clause predicates and
  unsupported cut placements remain unchanged. These syntactic transformations
  are not machine-checked proofs. Finite built-in
  `member/2` calls over ground proper lists are also classified for variable,
  ground, and partially instantiated element patterns, preserving duplicate
  successes without binding the analyzed program; `select/3` over ground proper
  lists counts duplicate positions and matches partially instantiated
  value/remainder patterns on copies;
  `select/3` with three distinct unbound arguments, supported unbound-list
  patterns, and `member/2` over an unbound list are classified as multi or
  deterministic for their supported independent patterns;
  and `length/2` calls
  over ground proper lists are classified when the length is unbound or a
  nonnegative integer, while variable lists with fixed nonnegative lengths are
  classified as deterministic; distinct unbound list and length variables are
  classified as multi. Ground proper-list `nth0/3` and `nth1/3` calls are
  classified for variable or integer indices and arbitrary element patterns,
  preserving pattern and index/element sharing, zero-/one-based indexing, and
  duplicate-position counts. `append/3`
  is classified as multi when all three
  arguments are distinct unbound variables, and as deterministic or failing
  when all three arguments are ground proper lists or one argument is unbound
  and the other two are ground proper lists. With two distinct unbound arguments
  and a ground proper-list result, empty input is deterministic and nonempty
  input is multi; the two modes with an unbound output and one ground input are
  also multi. See
  [`docs/detlog.md`](docs/detlog.md).
- **Detlog `once/1` compilation (restricted):** lowers `once/1` over a
  documented pure built-in/control-flow subset, including built-in `member/2`,
  `between/3`, `length/2`, `nth0/3`, `nth1/3`, `append/3`, and `select/3`, to IR
  if-then-else, preserving unsupported and locally defined predicates unchanged.
  It also removes a redundant green cut in a single-clause predicate after a
  conjunction of deterministic built-ins; other cuts are kept.
  It does not yet implement choicepoint splicing, choice packets, or general
  cut conversion. See
  [`docs/detlog.md`](docs/detlog.md).
- **loop2 conversion:** converts `findall/3` over ground facts, `member/2`,
  `select/3`, or `append/3` on a ground proper list, `nth0/3` or `nth1/3` on a
  ground proper list, bounded `between/3` ranges, or `length/2` on a ground proper list,
  optionally with supported arithmetic filters, into deterministic list-copy
  loops. Bound or partially instantiated arguments are matched against fact and
  rule heads or list-generator patterns. List order, selection remainders,
  indices, duplicates, and supported nested `findall/3` values in finite acyclic
  rules are preserved; unsupported generators remain
  unchanged, and the conversion report is an obligation—not an independently
  checked proof.
  See [`docs/loop2.md`](docs/loop2.md).
- **PLOp pipeline (initial slice; see [plop2](https://github.com/luciangreen/plop2) for per-character PLOp):** whole-program and single-predicate entry
  points reuse the finite-generator conversion and apply multiple conversions
  only when the independent proof checker accepts the complete sequential proof.
  Unsupported or ambiguous cases are left unchanged. It does not yet implement
  closed-form discovery, a cost model, or the general PLOp rewrite set. See
  [`docs/current_features.md`](docs/current_features.md#plop-pipeline).
- **Quantum-inspired search (initial slice):** deterministically compares the
  original program with proof-checked whole-program and per-predicate PLOp
  candidates, records amplitude updates and optional linked-predicate proof
  rechecks, and can emit a schematic OpenQASM 3 selection register. It does not
  search arbitrary rewrite sequences or execute quantum circuits. See
  [`docs/quantum.md`](docs/quantum.md).
- **AlgebraPLOp (initial slice):** deterministically recognizes exact constant,
  affine, quadratic, higher-degree integer polynomial, and integer-base geometric
  sequences and checks all provided samples, including held-out samples for fitted
  formulas. Exact inverse lookup is available for constant, affine, and
  integer-base geometric and polynomial formulas. Supported formulas can also be
  evaluated at exact nonnegative positions; program positions and proof-backed
  formulas remain unsupported here (see
  [algebraplop2](https://github.com/luciangreen/algebraplop2) for those). See
  [`docs/current_features.md`](docs/current_features.md#algebraplop-sequence-inference).
- **S2A (initial inference):** for two or more distinct ground examples, a
  unique input subterm address shared with every output generates a generalized
  projection clause; otherwise integer examples may infer an exact integer-affine,
  integer-quadratic, or integer-cubic relation. Ambiguous or unsupported cases are reported
  unless `[allow_table(true)]` explicitly permits a lookup table. These
  candidates reproduce the examples but have no formal proof certificate;
  recursive generalization and broader arithmetic templates remain unsupported.
  See [`docs/current_features.md`](docs/current_features.md#s2a-synthesis).
- **S2A2 bridge:** `mnn_s2a2:s2a2/4` takes the same spec. When `s2a/4` finds
  nothing, it asks [S2A2](https://github.com/luciangreen/S2A2)'s `io_synth` for
  a program (lists, recursion, invented helper predicates) and returns it in the
  IR. Given a reference program, it adds an mnns `induction_equivalence` proof
  that the checker re-proves. It also runs S2A2's optimisation (`learn/2`,
  `apply_algorithm/5`, and `fold.pl`'s derivations) on IR programs. On 12 shared
  tasks `s2a/4` solves 4 and S2A2 all 12. See [`docs/s2a2.md`](docs/s2a2.md).
- **Starlog (initial readable view):** translates declared or module-qualified
  function expressions to predicate calls, and supports string (`:`), list (`&`),
  and atom (`•`) concatenation. Type coercion is opt-in; broader Starlog syntax
  and reverse conversion of ambiguous ordinary predicate calls remain limited.
  See [`docs/starlog.md`](docs/starlog.md).
- **AIOC structural size metric (initial):** reports clause, goal, predicate, and
  term-node counts for an IR program, plus an equal-weight total. This measures
  representation size only; it does not estimate runtime or memory cost. A
  restricted data-only decision-tree front end compiles pure type checks and
  numeric comparisons to the shared IR and carries an independently checked
  canonical-translation proof. Restricted data-only CFG and DCG front ends
  compile terminal/nonterminal productions into shared IR and carry
  independently checked canonical-translation proofs. The DCG front end
  supports terminal lists, atom nonterminals, conjunction, disjunction, and
  epsilon productions; arbitrary DCG goals and broader source-form
  incorporation remain unimplemented. An initial proof-checked simplifier
  removes explicit `true` conjuncts and `fail` disjuncts and collapses
  redundant `once(true)` / `once(fail)` wrappers,
  independently checking each rewrite; it does not yet perform general
  dead-code or semantic simplification. An
  initial proof-gated comparison reports candidate-versus-original structural
  change and deterministic ranking of supplied candidates are available only
  after the independent checker accepts each proof; ranking uses structural
  size, not runtime or quality. The
  resource allocator deterministically divides caller-supplied time, memory,
  worker, depth, data, and effort budgets according to candidate assessment/cost
  scores, with optional amplitude weighting. It plans integer shares only; it
  does not dispatch workers or enforce machine resource limits. The
  proof-checked library records candidate metadata and test-result claims, then
  rechecks proofs when entries are retrieved, updated, or included in a
  library-wide structural assessment; named entries can be removed, and
  `rank_library/2` ranks proof-checked entries by structural size. Named test
  suites can be persisted as data and run against proof-rechecked entries through
  the bounded sandbox; passing results can be recorded. Suite files and result
  terms are editable and not cryptographically authenticated. These example
  checks are not proofs, and the library does not assess runtime or qualitative
  properties.
  The bundle writer and verifier emit and re-check only proof-certified bundles. See
  [`docs/aioc.md`](docs/aioc.md) and
  [`docs/bundle.md`](docs/bundle.md).

## Optimise a file in one command

`optimise.pl` runs every proof-checked optimisation stage in turn: PLOp's
finite-generator conversion, the AIOC simplifier, then Detlog's cut and
`once/1` rewrites, each checked by the `remove_green_cut`, `compile_cut` and
`compile_once` proof rules. If a stage's proof is not accepted, that stage
leaves the program unchanged.

```sh
swipl optimise.pl -- input.pl output.pl
```

The `--` stops `swipl` from loading `input.pl` and `output.pl` as program files.

It prints one line, which tools such as
[fastos](https://github.com/luciangreen/fastos) read:

```
MNN_OPTIMISE ok changed=true size_before=40 size_after=36 plop=accepted simplify=0 detlog=unchanged detlog_steps=0
```

If the input uses syntax outside the supported subset, it prints
`MNN_OPTIMISE error ...`, exits with status 1 and writes nothing. From Prolog,
use `mnn_optimise:optimise_file/3` or `mnn_optimise:optimise_program/3`
([`prolog/optimise/optimise.pl`](prolog/optimise/optimise.pl)).

## Requirements

Install SWI-Prolog 9.x or 10.x. On Debian or Ubuntu:

```sh
sudo apt-get install swi-prolog-nox
```

## Tests

Run the full Prolog test suite from the repository root:

```sh
swipl -q -s tests/run.pl
```

The runner loads the IR, proof checker, round-trip corpus, sandbox runner, PID,
loop2, Detlog, PLOp, AlgebraPLOp, S2A, Starlog, AIOC size-metric,
decision-tree, CFG and DCG incorporation, simplifier, assessment, bundle,
resource-allocation, library, bounded test-runner, and quantum-search tests. Focused
commands for every PlUnit group are listed in
[`docs/current_features.md`](docs/current_features.md). For example:

```sh
swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
swipl -q -g "load_files('tests/plop_tests.pl'), run_tests(mnn_plop), halt"
swipl -q -g "load_files('tests/optimise_tests.pl'), run_tests(mnn_optimise), halt"
```

If your shell uses an ASCII `C` locale, prefix Prolog commands with
`LC_ALL=C.UTF-8` because the Starlog tests exercise Unicode operators.

The full suite is also run on pushes and pull requests by
[`.github/workflows/prolog-tests.yml`](.github/workflows/prolog-tests.yml).
More detail on current capabilities and limitations is in
[`docs/current_features.md`](docs/current_features.md), including focused
commands for every implemented test group.


* Manual Neuronets (MNNs) are Green's invention and a way to represent the hidden workings of black-box neural nets. They combine the [Spec to Algorithm](https://github.com/luciangreen/Philosophy/tree/master/s2a), [Starlog](https://github.com/luciangreen/Starlog), [Prolog Inductive Debugger](https://github.com/luciangreen/Prolog_Inductive_Debugger), [loop2](https://github.com/luciangreen/loop2), [PLOp2](https://github.com/luciangreen/plop2)/[AlgebraPLOp2](https://github.com/luciangreen/algebraplop2), [Detlog2](https://github.com/luciangreen/detlog2), and [Piglog2](https://github.com/luciangreen/piglog2) repositories. Later, a chatbot incorporating natural language, manual attention, manual time series and other aspects of NNs such as signposting, ranking, analysis, conversations and personality overlays will be added.

## Inputs and outputs

`io/ios.txt` lists 200 inputs and the outputs they give, from real runs of this repo's predicates (which predicates, and how the inputs are made, is in `io/cases.pl`; the inputs are made the same way every time). `swipl io/check_ios.pl` runs them again and fails if any output changed; the "Inputs and outputs" workflow does the same on every push. If a change is meant, run `swipl io/make_ios.pl` and check the diff.

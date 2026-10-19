# Manual Neuronets

MNN Suite is an in-progress SWI-Prolog implementation of proof-carrying
optimisations for Prolog algorithms. It represents programs in a shared
intermediate representation (IR), runs them in a bounded sandbox, and includes
early implementations of an independent proof checker, termination analysis,
and finite-generator loop conversion.

This repository implements only a subset of the full vision in
[`PROGRAM_REQUIREMENTS.md`](PROGRAM_REQUIREMENTS.md). It includes an initial
Detlog analysis but not Detlog transformations, and does not yet provide the
end-user MNN compiler, S2A/Starlog, PLOp, AIOC, neural-network, chatbot, or agent
features. See [`PROGRESS.md`](PROGRESS.md) for the current implementation and
remaining work.

## Implemented features

- **IR parser and emitter:** reads Prolog clauses and directives into
  `mnn_program/5`, preserves clause order and source locations, normalizes
  control-flow goals and `once/1` bodies, and emits Prolog. Explicit `call/N`
  goals are rejected.
- **Sandboxed runner:** strips source directives, checks requested goals with
  SWI-Prolog's sandbox, and limits execution time and answer count. See
  [`prolog/runner/sandbox_runner.pl`](prolog/runner/sandbox_runner.pl).
- **Proof checker and renderer:** independently checks identity, one adjacent
  reordering of restricted ground type tests, restricted definition
  introduction, narrow single-occurrence unfold/fold steps, and `findall/3`
  conversions over ground facts, `member/2`, `select/3`, `nth0/3`, and `nth1/3`,
  with supported arithmetic-comparison filters. It also checks filtered and
  no-filter conversions over `length/2`, plus bounded `between/3` conversions with or
  without supported arithmetic-comparison filters, and finite acyclic rule
  generators with restricted pure bodies. The `nth0/3` and `nth1/3`
  filter cases require distinct unbound index and element variables. Selection
  order, fact order, and duplicate answers are preserved; indices are checked
  as zero-based for `nth0/3` and one-based for `nth1/3`. Unsupported proof rules and
  broader findall conversions are rejected.
  See [`docs/proof_rules.md`](docs/proof_rules.md).
- **PID analysis:** classifies recursive predicates, checks a limited set of
  shared structural and guarded natural-number decreases, and emits schematic
  induction obligations for supported measures; it also identifies syntactic
  tail recursion. These analyses are not proofs of a specification or full
  termination. See [`docs/pid.md`](docs/pid.md).
- **Detlog analysis:** conservatively classifies success counts for a limited
  set of normalized goals when all predicate arguments are unbound. Unsupported
  goals are reported rather than guessed; acyclic user-predicate calls with
  distinct unbound arguments are analyzed recursively, ground whitelisted
  built-ins are evaluated for success or failure, bounded literal `between/3`
  calls are classified, and `once/1` caps reported successes at one. Choicepoint
  and cut transformations are not implemented yet. Finite built-in
  `member/2` calls over ground proper lists are also classified for variable,
  ground, and partially instantiated element patterns, preserving duplicate
  successes without binding the analyzed program; `select/3` over ground proper
  lists counts duplicate positions and honors ground value/remainder patterns;
  `member/2` over an unbound list is classified as multi when the element pattern
  does not alias that list;
  and `length/2` calls
  over ground proper lists are classified when the length is unbound or a
  nonnegative integer, while variable lists with fixed nonnegative lengths are
  classified as deterministic. Ground proper-list `nth0/3` and `nth1/3` calls are
  classified for variable or integer indices and variable or ground elements,
  preserving zero-/one-based indexing and duplicate-position counts. `append/3`
  is classified as multi when all three
  arguments are distinct unbound variables, and as deterministic or failing
  when all three arguments are ground proper lists or one argument is unbound
  and the other two are ground proper lists. With two distinct unbound arguments
  and a ground proper-list result, empty input is deterministic and nonempty
  input is multi; the two modes with an unbound output and one ground input are
  also multi. See
  [`docs/detlog.md`](docs/detlog.md).
- **loop2 conversion:** converts `findall/3` over ground facts, `member/2` or
  `select/3` on a ground proper list, `nth0/3` or `nth1/3` on a ground proper
  list, bounded `between/3` ranges, or `length/2` on a ground proper list,
  optionally with supported arithmetic filters, into deterministic list-copy
  loops. Bound or partially instantiated arguments are matched against fact and
  rule heads or list-generator patterns. List order, selection remainders,
  indices, and duplicates are preserved; unsupported generators remain
  unchanged, and the conversion report is an obligation—not an independently
  checked proof.
  See [`docs/loop2.md`](docs/loop2.md).

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
loop2, and Detlog tests. Focused commands for every PlUnit group are listed in
[`docs/current_features.md`](docs/current_features.md). For example:

```sh
swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
```

The full suite is also run on pushes and pull requests by
[`.github/workflows/prolog-tests.yml`](.github/workflows/prolog-tests.yml).
More detail on current capabilities and limitations is in
[`docs/current_features.md`](docs/current_features.md).

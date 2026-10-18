# Manual Neuronets

MNN Suite is an in-progress SWI-Prolog implementation of proof-carrying
optimisations for Prolog algorithms. It represents programs in a shared
intermediate representation (IR), runs them in a bounded sandbox, and includes
early implementations of an independent proof checker, termination analysis,
and finite-generator loop conversion.

This repository implements only a subset of the full vision in
[`PROGRAM_REQUIREMENTS.md`](PROGRAM_REQUIREMENTS.md). In particular, it does not
yet provide the end-user MNN compiler, S2A/Starlog, Detlog, PLOp, AIOC,
neural-network, chatbot, or agent features. See [`PROGRESS.md`](PROGRESS.md) for
the current implementation and remaining work.

## Implemented features

- **IR parser and emitter:** reads Prolog clauses and directives into
  `mnn_program/5`, preserves clause order and source locations, normalizes
  control-flow goals, and emits Prolog. Explicit `call/N` goals are rejected.
- **Sandboxed runner:** strips source directives, checks requested goals with
  SWI-Prolog's sandbox, and limits execution time and answer count. See
  [`prolog/runner/sandbox_runner.pl`](prolog/runner/sandbox_runner.pl).
- **Proof checker and renderer:** independently checks identity, one adjacent
  reordering of restricted ground type tests, restricted definition
  introduction, and narrow single-occurrence unfold/fold steps. Unsupported
  rules are rejected. See [`docs/proof_rules.md`](docs/proof_rules.md).
- **PID analysis:** classifies recursive predicates, checks a limited set of
  shared structural and guarded natural-number decreases, and emits schematic
  induction obligations for supported measures. These are not proofs of a
  specification. See [`docs/pid.md`](docs/pid.md).
- **loop2 conversion:** converts `findall/3` over ground facts, optionally with
  supported arithmetic filters, into deterministic list-copy loops. Other
  generators remain unchanged, and the conversion report is an obligation—not
  an independently checked proof. See [`docs/loop2.md`](docs/loop2.md).

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
and loop2 tests. To run one PlUnit group in isolation, for example:

```sh
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
swipl -q -g "load_files('tests/pid_tests.pl'), run_tests(mnn_pid), halt"
swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"
```

The full suite is also run on pushes and pull requests by
[`.github/workflows/prolog-tests.yml`](.github/workflows/prolog-tests.yml).
More detail on current capabilities and limitations is in
[`docs/current_features.md`](docs/current_features.md).

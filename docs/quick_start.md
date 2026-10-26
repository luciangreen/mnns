# MNN Suite quick start

MNN Suite is an in-progress SWI-Prolog project. This guide gets you from a
working Prolog installation to running the parser, sandboxed runner, and tests.
For the complete list of implemented features and focused test commands, see
[`current_features.md`](current_features.md). For the remaining work by stage,
see [`../PROGRESS.md`](../PROGRESS.md).

## Install

The project requires SWI-Prolog 9.x or 10.x. On Debian or Ubuntu:

```sh
sudo apt-get install swi-prolog-nox
```

Run the commands below from the repository root.

## Parse and emit a program

The corpus includes small Prolog programs covering the parser's supported
syntax. This command parses a program into the shared IR and emits its terms
back to the terminal:

```sh
swipl -q -g "use_module('prolog/ir/ir'), mnn_ir:parse_program('tests/corpus/recursive_rules.pl', Program), mnn_ir:ir_to_prolog(Program, Terms), maplist(writeln, Terms), halt"
```

The parser and emitter interfaces are `mnn_ir:parse_program/2`,
`mnn_ir:ir_to_prolog/2`, and `mnn_ir:emit_program/2`. The supported source
subset and its round-trip corpus are described in the
[feature guide](current_features.md#program-ir).

## Run a program in the sandbox

The sandbox runner strips directives, checks the requested goal, and applies
time and answer limits. For example, this runs the corpus's recursive
`ancestor/2` predicate:

```sh
swipl -q -g "use_module('prolog/runner/sandbox_runner'), mnn_sandbox_runner:run_program('tests/corpus/recursive_rules.pl', ancestor(ada, Who), [max_answers(10)], answers(Answers)), writeln(Answers), halt"
```

See [sandboxed execution](current_features.md#sandboxed-execution) for the
available options and limitations.

## Run tests

Run every PlUnit test group, including the round-trip corpus:

```sh
swipl -q -s tests/run.pl
```

To focus on one subsystem, load its test file and run its named test group. For
example:

```sh
swipl -q -g "load_files('tests/proof_checker_tests.pl'), run_tests(mnn_proof_checker), halt"
swipl -q -g "load_files('tests/loop2_tests.pl'), run_tests(mnn_loop2), halt"
swipl -q -g "load_files('tests/plop_tests.pl'), run_tests(mnn_plop), halt"
```

[`current_features.md#feature-and-test-map`](current_features.md#feature-and-test-map)
lists the focused command for every implemented test group. The full suite is
also run by CI on pushes and pull requests.

## Implementation status

Stages 1–9 have partial implementations; stages 10–14 have not started. The
implemented slices include the shared IR and sandbox runner, restricted proof
checking, PID and Detlog analysis, finite-generator loop conversion, an initial
proof-gated PLOp pipeline, sequence inference, S2A example synthesis, an initial
Starlog function-expression view, restricted AIOC decision-tree and CFG
incorporation, size measurement, proof-gated structural comparison, and
proof-checked bundles.
The full optimization chain,
general synthesis and proof rules, the broader Starlog language, ANN/AMNN
generation, Neuroprolog, the MNN chatbot and agent, and benchmark suite are not
yet complete. See
[`../PROGRESS.md`](../PROGRESS.md) for the detailed feature-by-feature status
and remaining acceptance work.

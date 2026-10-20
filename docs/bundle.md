# MNN bundles

`mnn_aioc_bundle:write_bundle/3` writes a proof-checked bundle from existing IR:

```prolog
write_bundle(mnn_bundle(Program, Original, Proof, Trace, Report),
             OutputDirectory,
             Name).
```

`Program` is the candidate MNN IR and `Original` is its source IR. `Proof` must
be accepted by the independent proof checker before any files are written.
`Trace` must be ground Prolog data, and `Report` must be a string supplied by
the caller. The output directory is created if needed. `Name` must be an atom
containing only letters, digits, underscores, or hyphens.

For `Name = sample`, the writer produces:

| File | Contents |
| --- | --- |
| `sample.pl` | The candidate emitted as standalone Prolog |
| `sample.original.pl` | The original emitted as Prolog |
| `sample.proof.pl` | A `bundle_proof(Program, Original, Proof)` data term |
| `sample.proof.md` | The proof renderer's independently checked explanation |
| `sample.trace.pl` | The supplied ground trace term |
| `sample.report.md` | The supplied report text |

`mnn_aioc_bundle:check_bundle/3` reads these files as data and re-checks the
proof:

```prolog
check_bundle(OutputDirectory, Name, accepted).
```

It parses both Prolog files without consulting or executing them, verifies that
their terms match the IR snapshots stored with the proof, then calls the
independent checker. A missing file, modified program, malformed proof
envelope, or rejected proof produces a rejection result; malformed source or
data can raise a parsing error. This is a bundle writer and verifier, not the
full `mnn_compile/3` or `mnn_check/2` command-line/REPL interface. It does not
generate an optimization report or trace, and optional AMNN/ANN files are not
implemented.

Run the focused bundle tests from the repository root:

```sh
swipl -q -g "load_files('tests/bundle_tests.pl'), run_tests(mnn_aioc_bundle), halt"
```

Run all test groups with:

```sh
swipl -q -s tests/run.pl
```

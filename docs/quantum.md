# Quantum-inspired search (initial slice)

`mnn_qi_search:qi_search/4` builds a bounded candidate set from the existing
proof-gated PLOp pipeline. It tries the whole-program optimizer and each
single-predicate entry point, independently checks every returned proof against
the original IR, and admits only accepted candidates. The original program is
included with an identity proof. Duplicate program variants are retained once.

```prolog
mnn_qi_search:qi_search(
    Program,
    [seed(42), links([qi_link(values/1, number/1)])],
    Best,
    Report).
```

The options are:

- `seed(NonNegativeInteger)`, default `0`. It deterministically varies initial
  candidate amplitudes; it does not invoke a quantum or stochastic backend.
- `links([qi_link(PredA, PredB), ...])`, default `[]`. Both predicate keys must
  exist in the input program. When a single-predicate proposal changes one end
  of a link, the search rechecks that proposal's complete proof and records the
  linked predicate and result in the history.

The report is `qi_report(Seed, Links, Candidates, History,
selected(Name), FinalSize, proof_steps(Count),
rewrites_tried(Count))`. Each candidate summary is
`candidate(Name, Program, Proof, amplitude(Amplitude), cost(Size))`; history
events retain the proposed program, including proposals rejected by the proof
checker. `rewrites_tried/1` counts the whole-program and per-predicate PLOp
entry-point proposals, not individual findall conversions. A checked size
reduction amplifies a proposal; non-reducing proposals are attenuated. The
history records proof status, structural cost, linked rechecks, and
supporting/opposing evidence. The final selection is deterministic: highest
amplitude, then lowest structural size, then candidate name. The chosen proof is
checked again before `Best` is returned. Structural size is the representation
metric documented in [`aioc.md`](aioc.md); this search does not estimate
runtime or memory.

This is not yet a general search over rewrite sequences: it only explores
whole-program and one-predicate applications of the current PLOp conversion
pipeline. Amplitudes are deterministic bookkeeping, not quantum amplitudes,
and no quantum execution or advantage is claimed. Classical-versus-search
benchmark timing, proof-size comparisons, richer rewrite operators, and
OpenQASM execution remain future work.

`mnn_qi_search:qi_export(Program, qasm, File)` writes a schematic OpenQASM 3
predicate-selection register with one qubit per predicate (or one placeholder
qubit for an empty program). It records no executable optimizer and does not
run a circuit. Export failures are surfaced by SWI-Prolog's file errors.

Run the focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/qi_search_tests.pl'), run_tests(mnn_qi_search), halt"
```

The tests are included in the full suite:

```sh
swipl -q -s tests/run.pl
```

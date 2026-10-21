# AIOC structural size metric

`mnn_aioc_size:measure_program_size/2` reports structural counts for an
`mnn_program/5`:

```prolog
program_size(clauses(ClauseCount),
             goals(GoalCount),
             predicates(PredicateCount),
             term_nodes(TermNodeCount),
             weighted_total(WeightedTotal))
```

Each predicate record and clause record contributes one to its corresponding
count. Goal counts include each normalized goal and each control-flow node:
conjunction, disjunction, if-then-else, negation, and `once/1`; `true` and
`fail` each count as one goal. Term-node counts cover each clause head and body.
Variables contribute zero nodes, while each atomic or compound term contributes
one node, in addition to the nodes in its arguments. The weighted total sums
the four reported counts with weight one for each.

This is a deterministic representation-size metric, not an inference-count,
runtime, or memory estimate. It does not establish equivalence, assess candidate
quality, or simplify programs. See the initial proof-checked comparison below
and the [library documentation](#proof-checked-library).
The initial proof-checked bundle writer and verifier are described in
[`bundle.md`](bundle.md).

## Proof-gated structural comparison

`mnn_aioc_assessment:assess_candidate/4` independently checks a supplied proof
before comparing the original and candidate IR sizes:

```prolog
assess_candidate(Candidate, Original, Proof, Assessment).
```

For an accepted proof, `Assessment` is
`assessment(accepted, size_comparison(OriginalSize, CandidateSize,
weighted_delta(Delta), structural_effect(Effect)))`. `Delta` is the
candidate's weighted total minus the original's, and `Effect` is `smaller`,
`unchanged`, or `larger`. If the proof is rejected, the result is
`assessment(ProofResult, not_assessed)` and sizes are not compared.

This reports only a change in the documented structural metric. It does not
estimate runtime or memory, establish that a candidate is faster or better, or
apply or incorporate a candidate. A proof establishes only the equivalence
covered by the proof checker's supported rules.

Run its focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/aioc_size_tests.pl'), run_tests(mnn_aioc_size), halt"
swipl -q -g "load_files('tests/aioc_assessment_tests.pl'), run_tests(mnn_aioc_assessment), halt"
```

Run all test groups, including this one, with:

```sh
swipl -q -s tests/run.pl
```

## Proof-checked library

`mnn_aioc_library:store_entry/2` stores entries as data files in a library
directory:

```prolog
store_entry(Directory,
            mnn_library_entry(Name, Program, Original, Proof, Assessment,
                              Cost, Cycle, SourceForm,
                              [test_result(full_suite, passed)])).
```

The supplied proof must be accepted by the independent checker before writing.
Assessment, cost, cycle, source form, and test-result metadata must be ground,
and every recorded test result must be marked `passed`. Names contain only
letters, digits, underscores, and hyphens. Existing names cannot be overwritten.
These test results are caller-supplied metadata: the library does not execute
programs or test suites and cannot authenticate that the recorded tests ran.

`get_entry(Directory, Name, Result)` reads the entry as a Prolog term, never
consults it, and checks its proof again. It returns `accepted(Entry)` when
verified and `rejected(Reason)` for missing, malformed-shape, or unproved
entries. `list_entries(Directory, Names)` returns sorted names for files with
the library suffix; each should be fetched with `get_entry/3` before use.
Malformed Prolog data may raise a read error. Automatic test execution and
ranking are not implemented.

`update_entry(Directory, Entry, Result)` accepts a replacement only after
validating its shape and metadata and independently rechecking its proof. It
replaces an existing entry and returns `updated`; if the entry name is absent,
it returns `rejected(missing_entry)` without creating a new entry. The new term
is written to a temporary file in the same directory and renamed into place
after the write succeeds. Invalid entries and unaccepted proofs raise the same
domain errors as `store_entry/2`.

`remove_entry(Directory, Name, Result)` deletes a named file and returns
`removed`. It returns `rejected(missing_entry)` when the file is absent and
`rejected(invalid_name(Name))` when the name fails the library's name rules.
Removal does not read or execute the stored term.

`assess_library(Directory, Assessments)` visits stored entries in sorted name
order, reads each entry as data, rechecks its proof, and reports the existing
proof-gated structural comparison between its candidate and original. Each
result has the form `entry_assessment(Name, Assessment)`. A rejected entry is
reported as `entry_assessment(Name, rejected(Reason))`; accepted entries contain
the same `assessment(accepted, size_comparison(...))` result as
`mnn_aioc_assessment:assess_candidate/4`. This is a library-wide structural
assessment only: it does not execute tests, rank entries by runtime or quality,
or authenticate the stored test-result metadata. Invalid Prolog syntax can still
raise a read error.

Example calls, assuming `UpdatedEntry` is a valid entry term:

```prolog
mnn_aioc_library:update_entry('/path/to/library', UpdatedEntry, updated).
mnn_aioc_library:remove_entry('/path/to/library', old_name, removed).
mnn_aioc_library:assess_library('/path/to/library', Assessments).
```

Run the focused library tests from the repository root:

```sh
swipl -q -g "load_files('tests/aioc_library_tests.pl'), run_tests(mnn_aioc_library), halt"
```

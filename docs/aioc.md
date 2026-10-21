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
quality, simplify programs, or incorporate them into a library. These broader
AIOC capabilities remain future work; see [`PROGRESS.md`](../PROGRESS.md).
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

## Proof-gated cost/size candidate frontier

`mnn_aioc_assessment:assess_candidates/3` compares a set of candidate programs
using caller-supplied costs and the documented structural-size metric:

```prolog
assess_candidates(Candidates, Frontier, Results).
```

Each input is `candidate(Id, Program, Original, Proof, Cost)`. IDs must be
ground and unique. Costs must be nonnegative finite numbers supplied by the
caller; this feature does not estimate cost. Every candidate is checked
independently before its size can affect selection. Invalid proofs are reported
as rejected and are never selected. `Frontier` contains the IDs of accepted
candidates that are not dominated, in input order. Candidate A dominates B
when A's cost and structural size are both no greater than B's and at least one
is strictly lower. Candidates tied on both measures are all retained.

Each result is `candidate_result(Id, accepted(cost(Cost), structural_size(Size),
structural_effect(Effect), frontier(Status)))`, where `Status` is `selected` or
`dominated`; a failed proof is reported as
`candidate_result(Id, rejected(ProofResult))`. This implements only the
proof-gated cost/size portion of candidate comparison. Qualitative assessment,
the cost model, allocation, library incorporation, and full AIOC cycle logic
remain future work.

Run its focused tests from the repository root:

```sh
swipl -q -g "load_files('tests/aioc_size_tests.pl'), run_tests(mnn_aioc_size), halt"
swipl -q -g "load_files('tests/aioc_assessment_tests.pl'), run_tests(mnn_aioc_assessment), halt"
```

Run all test groups, including this one, with:

```sh
swipl -q -s tests/run.pl
```

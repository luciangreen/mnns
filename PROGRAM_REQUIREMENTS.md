# MNN Suite — Prolog Program Requirements

Requirements for a GitHub coding agent (Copilot Agent or equivalent) to implement
the MNN Suite in SWI-Prolog.

Suggested repository name: `mnn-suite`

Suggested repository description (GitHub "About", under 350 characters):

> SWI-Prolog suite that turns algorithms or S2A specs into Manual Neuronets
> (MNNs): the original algorithm with optimisations chosen by the AIOC
> controller, each with a checked proof. Also builds ANN and AMNN forms, with
> quantum-inspired search, Neuroprolog mode, an MNN chatbot and a sandboxed
> agent.

---

## 1. Explanatory description

### 1.1 What an MNN is

A **Manual Neuronet (MNN)** is an original Prolog algorithm with the MNN
optimisations applied. The algorithm stays readable Prolog; the optimisations
make it smaller, more deterministic and faster, and every optimisation carries a
proof that the result computes the same answers as the original.

The suite takes either:

- an ordinary Prolog program (the **original algorithm**), or
- an S2A specification (input/output examples), from which S2A synthesises the
  original algorithm,

and produces an **MNN bundle**: the optimised program, its proof, a
human-readable explanation and a trace of every transformation.

From an MNN the suite can also produce:

| Form | What it is | Correctness claim |
| --- | --- | --- |
| **MNN** | Original Prolog algorithm + proved optimisations | Proved equivalent to the original on the stated domain |
| **AMNN** (Artificial Manual Neuronet) | A neural network whose neurons, weights and thresholds are *derived by hand-style compilation* from the MNN, not learned | Proved equivalent on a stated finite or discretised domain, or not issued |
| **ANN** (Artificial Neural Network) | A conventional weighted network trained by (manual, traced) gradient descent to imitate the MNN | Approximate; error measured and reported; never labelled proved unless exhaustively verified on a finite domain |

### 1.2 The optimisation chain

The suite reimplements, inside one repository and one shared representation,
the parts listed in the [mnns](https://github.com/luciangreen/mnns) README, and
adds quantum-inspired optimisations. The whole chain is driven by **AIOC**, a
six-stage controller (§4.9):

```
AIOC 1  INCORPORATE   Prolog program │ decision tree │ CFG │ S2A spec ──► MNN IR
                      (S2A synthesises Prolog from specs; Starlog is the editing view)
                          │
AIOC 2  OPTIMISE      PID: termination + induction obligations
                      loop2: findall/member → deterministic loops
                      Detlog: choicepoints → splices, cuts → decisions
                      PLOp: unfold, memoise, hoist, closed forms, indexing
                      AlgebraPLOp: positional formulas, inverses, r-specs
                      Quantum-inspired search chooses which rewrites, where, in what order
                          │
AIOC 3  SIMPLIFY      minimise size/structure, preserving input/output behaviour
                          │
        PROOF CHECK   independent checker ──► reject any unproved step
                          │
AIOC 4  ASSESS        qualitative scores: clarity, explainability, modularity,
                      generality, robustness, maintainability, novelty, fit
                          │
AIOC 5  ALLOCATE      time, memory, workers, search depth, data, further effort
                          │
AIOC 6  CYCLE         compare candidates; proved structures from one become
                      rewrite rules/resources for others; feed results back ──► 2
                          │
                 algorithm library (only proved, assessed MNNs)
                          │
          ┌───────────────┼───────────────┐
         MNN            AMNN             ANN
                          │
          Neuroprolog mode (optional): Piglog2 grouping → concurrent groups
          run by separate ANNs/AMNNs
```

Each optimisation and simplification is a **proof-carrying rewrite**: it may
only change the program by applying rules whose correctness lemma is in the
suite, and it must emit the proof steps it used. A rewrite that cannot be proved
leaves the program unchanged and the reason is reported. "Faster" and "simpler"
are separate objectives: the optimise stage targets cost, the simplify stage
targets size and structure, and both results are kept when they differ.

### 1.3 What "correct" means

Correct means **an actual proof, documented with the program**. Tests are
required but are never accepted as evidence of correctness on their own.

- For a supplied Prolog program, the MNN is proved equivalent to that program
  (same answers, same order where order is declared significant, same failure
  and same errors) on a stated domain.
- For an S2A spec, the synthesised original algorithm is proved to reproduce
  every example exactly; optimisations are then proved equivalent to that
  synthesised algorithm. The suite never claims that a synthesised algorithm is
  the "true" function behind the examples.
- Proofs are machine-checkable terms checked by an independent checker module
  that shares no code with the optimisers, plus a rendered human-readable proof.

### 1.4 Quantum-inspired MNNs

Quantum ideas are used as **classical, explainable mechanisms**. The suite never
claims MNNs are physically quantum or that any quantum advantage exists.

| Quantum idea | MNN mechanism in this suite |
| --- | --- |
| Superposition | A candidate set: several rules, interpretations or rewrite sequences kept explicitly (choice packets) before selection |
| Measurement | Proof-gated selection: the candidate set collapses to the one candidate with a checked proof and lowest cost; the collapse is logged |
| Entanglement | Declared links between variables or rules; changing one propagates through all linked rules, with the propagation traced |
| Interference | Supporting and opposing derivation chains add or cancel weights to rank, prune or modify conclusions |
| Quantum parallelism | Independent branches evaluated concurrently (Neuroprolog mode) and recombined |
| State evolution | An MNN state that updates as observations arrive, keeping an auditable history (time series) |
| Quantum-inspired optimisation | Amplitude-style search over rewrite sequences (classical simulation of amplitude amplification) to find shorter deterministic MNNs |

Three architectures must be comparable on the same tasks: **classical MNN**,
**quantum-inspired MNN**, and **quantum-executed MNN** (an export interface
only in version 1; see §4.8).

### 1.5 Neuroprolog mode

Neuroprolog mode (in the LLM sense of a model made of cooperating parts) groups
the predicates of an algorithm or MNN into **concurrent** and **non-concurrent**
groups. Each group is executed by its own ANN or AMNN (with optimised code
behind it), and a deterministic coordinator combines the results. Piglog2-style
analysis is required only for this mode.

### 1.6 Applications built on MNNs

- **MNN chatbot** (after [MNN2](https://github.com/luciangreen/mnn2)): answers
  questions by running MNNs over recorded facts and returns the answer,
  evidence and trace separately.
- **MNN agent** (after [MNN3](https://github.com/luciangreen/mnn3)): plans and
  writes reviewed artifacts in a sandboxed workspace, using MNNs for planning
  steps.
- **MNN reasoning core** (after [MNN1](https://github.com/luciangreen/mnn1)):
  indexed facts, deterministic derivations, working memory and data traces.
- **Manual gradient descent**: gradient steps for ANNs computed symbolically,
  printed and steppable, so training is inspectable.

---

## 2. Scope

### 2.1 Included in version 1

- SWI-Prolog 9.x and 10.x, Linux and macOS, Windows best-effort.
- Pure Prolog source: facts, rules, conjunction, disjunction, if-then-else,
  negation as failure, cut, arithmetic, lists, strings, atoms, `findall/3`,
  `member/2`, `between/3`, `nth0/3`, `nth1/3`, `length/2`, `append/3`.
- Everything in §§4–14.

### 2.2 Excluded from version 1

- Running on quantum hardware (export only).
- Attributed variables, constraint libraries, tabling, global variables,
  `assert`/`retract` in the program being optimised (these predicates are kept
  as-is and reported, never optimised).
- I/O inside predicates being optimised (kept as-is, reported).
- Any network access, shell access or process spawning by the suite.
- The chatbot's broad natural-language understanding beyond §11.

### 2.3 Reimplementation policy

All parts are reimplemented in this repository. The original repositories are
references only; no code may be loaded from them at run time. Features are
added in **minimal and complete** steps: each feature, when added, must be
complete for its stated subset (proved, tested, documented), even if the subset
is small. A feature that is partial is not merged.

---

## 3. Shared representation (MNN IR)

All stages read and write one IR. No stage may define a private program format.

```prolog
mnn_program(Name, Meta, Predicates, Proof, Trace).

mnn_pred(Name/Arity, Mode, Domain, Clauses, Status).
  % Mode   : list of +, -, ? per argument (declared or inferred)
  % Domain : type per argument, e.g. [nat, any], [list(integer), integer]
  % Status : original | optimised(Stages) | kept(Reason)

mnn_clause(Id, Head, Body, SourceLoc).
  % Body is a normalised goal tree: conj/2, disj/2, ite/3, not/1, call/1-free

proof(Steps).       % list of proof_step/4, see §7
trace(Events).      % list of stage_event/4: stage, predicate, rule, result
```

Requirements:

- R3.1 `parse_program/2` reads a Prolog file into the IR, keeping source
  locations; `emit_program/2` writes valid, standalone Prolog (every predicate
  the output calls is either built in, defined in the output, or loaded by an
  explicit `use_module/1` directive in the output).
- R3.2 `ir_to_prolog/2` then `parse_program/2` must round-trip to an
  alpha-equivalent IR.
- R3.3 Variables are compared by identity (`==`), never by unification, in all
  analysis code. Clauses are renamed with `copy_term/2` before any splice or
  unfold.
- R3.4 No global mutable state (`assert`, `retract`, `nb_setval`, `b_setval`)
  in any stage. State is passed as arguments. Generated programs must be
  re-entrant: calling one twice with different inputs gives the same answers as
  calling it once with each input in a fresh process.

---

## 4. Part requirements

Each part lists its job, its required interface, and the acceptance tests it
must pass. Acceptance tests marked **[regression]** come from defects found in
the original repositories on 2026-10-18 and must never regress.

### 4.1 S2A — spec to original algorithm

Job: synthesise an original algorithm from S2A specs of the form
`[[input,[['A',Value]]],[output,[['B',Value]]]]`.

Interface: `s2a(Name, Spec, Options, mnn_program(...))`.

- R4.1.1 Find recurring structures, constants and unique variables; map each
  output position to an input address (sub-term with address).
- R4.1.2 Generalise list recursion across lengths (e.g. reverse learnt from
  lengths 3 and 4 applies to length 2).
- R4.1.3 Support arithmetic templates (affine maps, sums over lists) when the
  examples fix them uniquely; otherwise report `ambiguous(Candidates)`.
- R4.1.4 Output is ordinary Prolog in the IR, with a proof that it reproduces
  every example.
- R4.1.5 When no candidate fits, return `no_algorithm(Reason)`; never fall back
  to a lookup table silently (a lookup table is allowed only when the option
  `allow_table(true)` is given, and is labelled as such).
- Acceptance:
  - [regression] the README swap spec gives an algorithm that maps `[5,6]` to
    `[6,5]` and then `[7,8]` to `[8,7]` in the same session.
  - [regression] a generated predicate named `sum` does not collide with
    library predicates (generated code lives in its own module).
  - [regression] the test suite executes every generated algorithm on its
    examples and on held-out inputs; comparing generated text alone is not a test.

### 4.2 Starlog — readable view

Job: a two-way view `Out is f(Args)` ⇄ `f(Args, Out)` for editing MNNs.

- R4.2.1 `starlog_to_ir/2` and `ir_to_starlog/2` round-trip.
- R4.2.2 Operators `:` (string concat), `&` (append), `•` (atom concat).
- R4.2.3 User-defined predicates may be used as functions when declared with
  `:- starlog_function(Name/Arity)`.
- Acceptance:
  - [regression] `X is lists:reverse([1,2])` calls `lists:reverse/2`
    (module qualification is never read as string concatenation).
  - [regression] `X is 2:"a"` raises a type error unless coercion is enabled
    with an explicit option.

### 4.3 PID — termination and induction proofs

Job: prove termination and produce the induction obligations used by later
proofs. Reimplemented as a **proof generator**, not a checklist.

- R4.3.1 Find a well-founded measure for each recursive predicate: list length,
  term size, natural number decrease, or a user-declared measure. Mutual
  recursion is analysed over strongly connected components of the call graph.
- R4.3.2 Measures are checked symbolically on the clause body (the measure of
  every recursive call is strictly less, given the guards before it). Unbound
  arguments never satisfy a measure check.
- R4.3.3 Non-recursive predicates are not classified as recursive.
- R4.3.4 Optional checks: tail recursion; correctness against a user-supplied
  specification predicate (`pid_spec(Pred, SpecPred)`), proved by induction.
- Acceptance:
  - [regression] `count(0). count(N) :- N1 is N+1, count(N1).` is reported
    non-terminating (no decreasing measure).
  - [regression] `same([H|T]) :- same([H|T]).` is reported non-terminating
    within 1 second (the analysis itself always terminates).
  - [regression] `reverse(L,R) :- reverse_acc(L,[],R).` is reported as a
    non-recursive wrapper with no missing base case.
  - a predicate recursing on argument 2 is analysed on argument 2.

### 4.4 loop2 — findall to loops

Job: convert `findall/3` over finite generators into deterministic recursive
loops.

- R4.4.1 Generators: unary and n-ary facts, `member/2`, `between/3`,
  `nth0/3`/`nth1/3`, nested findall+member, single- and multi-clause rules.
- R4.4.2 Filters (goals that may fail per item) become skip clauses, not
  failing steps.
- R4.4.3 Bound generator arguments become filters.
- R4.4.4 Every loop predicate has a unique generated name.
- R4.4.5 All predicates not converted are kept in the output.
- R4.4.6 A clause whose body has goals besides the findall is converted in
  place; unsupported constructs affect only the predicate that contains them.
- Proof: each conversion cites the findall-to-fold lemma with the generator's
  finiteness and the transform's determinism as side conditions.
- Acceptance [regression]:
  - `findall(X,(num(X), X>1),R)` over `num(1..3)` gives `[2,3]`.
  - two findall predicates in one file produce two distinct loops.
  - a two-clause rule spliced into a findall keeps both clauses' answers.
  - `findall(x, colour(red), R)` gives `[x]` when `colour(blue)` also exists.
  - a cut in one predicate does not block conversion of another.

### 4.5 Detlog — determinism

Job: replace choicepoints with splices and choice packets, and cuts with
explicit decisions, preserving answers, order, duplicates and effects.

- R4.5.1 Mode and determinism inference per predicate (det, semidet, multi,
  nondet, failure).
- R4.5.2 Code generation must emit the runtime constructs: `splice/2`,
  `member_cp/2`, `decision/2`, `if_commit/3`, `once_det/1`.
- R4.5.3 Green cuts become `if_commit/3` or guarded clauses; red cuts are
  converted only with a proof that the guard is exhaustive and exclusive.
- R4.5.4 Fallback (calling the original) is allowed only with a diagnostic and
  is never counted as converted.
- Acceptance:
  - [regression] in the original Detlog sample, `det_sum/2`,
    `if_then_else/2` and `safe_cut/1` are converted, not fallen back.
  - converted predicates contain no operational cut.
  - answer sequences of source and output are identical on the test corpus.

### 4.6 PLOp — general optimiser

Job: base-up unfolding, memoisation, common-subgoal hoisting, hierarchical
splicing, list-to-formula, indexical/sub-term-address indexing, recursive index
loops, deterministic loop conversion, closed-form discovery.

- R4.6.1 One pipeline definition used by both whole-program and single-predicate
  entry points.
- R4.6.2 Closed-form discovery is general: from a recursion, derive candidate
  closed forms (polynomial fitting by exact Gaussian elimination over rationals
  is one source), then **prove** the closed form by induction on the measure
  from §4.3. Fitting alone never replaces code.
- R4.6.3 Rewrites keep the original's domain: if the original fails outside a
  domain (e.g. negative `N`), the output must fail there too (add the guard).
- R4.6.4 Index rewrites must not narrow data shapes (a row of length ≥ 2 must
  still be accepted if the original accepted it).
- Acceptance:
  - [regression] `sum_to_n(-3,S)` fails in the output as in the original.
  - [regression] `matrix_reconstruct` output runs standalone and accepts rows
    longer than 2.
  - [regression] `infer_sequence_formula/2` returns `no_formula` for
    `[2,3,5,7,11]` and for `[1,2,4,8,16,32]` unless held-out samples confirm the
    fit and a proof exists.
  - a recursion other than the exact `sum_to_n` text (e.g. sum of squares)
    receives a proved closed form.

### 4.7 AlgebraPLOp — positional algebra

Job: discover positional formulas and inverses, emit splice-index loops and
`r_spec` provenance.

- R4.7.1 Input may be a program (positions extracted from its index
  computations) as well as a sample term.
- R4.7.2 Discovery is deterministic: one answer, no choicepoints; candidates
  are ranked by a complexity penalty (minimum description length) and must
  pass held-out samples before a proof is attempted.
- R4.7.3 Report wording: `verified_on(Samples)` for checked samples,
  `proved(ProofId)` only with a checked proof.
- Acceptance:
  - [regression] samples `2,4,8,16` do not yield a piecewise linear formula;
    the result is `2^i` (if exponentials are enabled) or `no_formula`.
  - [regression] `complex_optimise_program/4` succeeds once, with no
    choicepoint.

### 4.8 Quantum-inspired optimisation

Job: search the space of rewrite sequences (which rule, where, in what order)
for the smallest proved MNN.

- R4.8.1 `qi_search(Program, Options, Best, Report)`: keeps a **candidate set**
  (superposition) of partially rewritten programs, each with an amplitude.
- R4.8.2 Amplitude update: candidates whose last rewrite was proved and
  reduced cost are amplified; failed or unproved ones are attenuated
  (interference). Supporting and opposing evidence are both recorded.
- R4.8.3 Entanglement: declared links (`qi_link(PredA, PredB)`) make a rewrite
  of one predicate schedule a re-check of linked predicates.
- R4.8.4 Measurement: selection of the final program is deterministic
  (highest amplitude, ties broken by cost then by name) and always proof-gated.
- R4.8.5 Seeded and reproducible; the full candidate history is in the trace.
- R4.8.6 `qi_export(Program, qasm, File)`: optional export of the selection
  problem as an OpenQASM 3 circuit description for later experiments. No
  quantum execution, no claim of advantage.
- Acceptance:
  - on the benchmark corpus (§13), report classical vs quantum-inspired:
    rewrites tried, final size, time, proof size. Either result is acceptable;
    the report must not overstate.

### 4.9 Proof checker and AIOC controller

- R4.9.1 `check_proof(Program, Original, Proof, Result)` re-checks every step
  independently. It must not import any optimiser module.

AIOC is the controller that runs the chain. Interface:
`aioc(Sources, Options, Library0, Library, Report)`, where `Sources` is a list of
candidate algorithms for the same task (one is allowed). Each stage writes its
decisions to the trace.

**AIOC 1 — Incorporate**

- R4.9.2 Accept an arbitrary algorithm and translate it into the MNN IR (§3).
  Required input forms: Prolog programs, decision trees
  (`dtree(Test, Yes, No)` / `leaf(Value)`), context-free grammars (DCG or
  `cfg(Start, Rules)`), and S2A specifications (via §4.1). Further forms are
  added as IR front ends, never as private formats.
- R4.9.3 Each translation carries a proof that the IR has the same input/output
  behaviour as the source form (for S2A: that it reproduces every example).
- R4.9.4 Incorporation reads input as data; it never executes the source.

**AIOC 2 — Optimise**

- R4.9.5 Search transformations to reduce cost: remove redundancy, factor common
  structures, memoise, reorder safe operations, identify recursion and loops,
  splice alternatives, apply known optimisation laws. The transformations are
  those of §§4.3–4.7; the search strategy is classical (deterministic order) or
  quantum-inspired (§4.8), chosen by option.
- R4.9.6 Cost model: estimated inference count by input size (symbolic where
  possible, measured on the benchmark inputs otherwise), plus memory. The model
  and its numbers appear in the report.

**AIOC 3 — Simplify**

- R4.9.7 Minimise the representation while preserving input/output behaviour:
  fewer clauses, goals, predicates and distinct constructs; merge equivalent
  clauses; remove dead code and unused arguments; fold repeated structure into
  shared predicates.
- R4.9.8 Size measure: weighted count of clauses, goals, predicates and term
  nodes, documented in `docs/aioc.md`.
- R4.9.9 When the fastest and the simplest versions differ, both are kept,
  each with its proof; the report shows the trade-off. The library entry names
  which one is the default and why.

**AIOC 4 — Qualitative assessment**

- R4.9.10 Score each proved candidate on: clarity, explainability, modularity,
  generality, robustness, maintainability, novelty and suitability for the
  stated problem.
- R4.9.11 Every score has a documented, deterministic measure (e.g.
  explainability = length of the readable trace for a typical input; modularity
  = predicates with a single responsibility over total; generality = size of the
  proved domain; novelty = structural distance from the nearest library entry;
  suitability = fit to the task's declared requirements). Optional human ratings
  can be added and are recorded separately from computed scores.
- R4.9.12 Assessment never overrides correctness: an unproved candidate is not
  assessed or incorporated.

**AIOC 5 — Resource allocation**

- R4.9.13 Assign compute time, memory, parallel workers, search depth, data
  (training/validation splits for ANNs) and further optimisation effort per
  candidate according to its assessment and cost, within global budgets set by
  options.
- R4.9.14 Allocation is deterministic for a given seed and budget, and every
  allocation decision is recorded with its reason.
- R4.9.15 In quantum-inspired mode, allocation follows candidate amplitudes;
  in Neuroprolog mode, it assigns groups to workers and executors.

**AIOC 6 — Cycle interaction**

- R4.9.16 Compare candidates for the same task on cost, size and assessment
  scores; keep a Pareto set rather than a single winner when no candidate
  dominates.
- R4.9.17 Transfer: a structure discovered in one candidate (a factored helper,
  a closed form, a loop shape, a rewrite sequence) may be generalised into a new
  rewrite rule or library resource for other candidates, but only after the
  generalised rule itself has a checked proof (a schema lemma). Unproved
  structures may be suggested in the report, never applied.
- R4.9.18 Feedback: measured results (actual costs, proof sizes, which rules
  helped) update the controller's rule priorities and allocation for the next
  cycle.
- R4.9.19 Termination: cycles stop at a fixed point (no candidate improves), at
  the budget, or at a cycle limit; the reason is reported.

**Library**

- R4.9.20 An MNN enters the algorithm library only if `check_proof/4` succeeds,
  all tests pass and its assessment is recorded. Library entries store the
  program, proof, assessment, cost, the cycle that produced it and its source
  form. Library files are data terms, read without executing them.
- Acceptance:
  - a decision tree, a DCG, an S2A spec and a Prolog program for the same task
    (e.g. classify an integer as negative, zero or positive) are all incorporated
    and proved equivalent to one another.
  - for `sum_to_n`, the report shows a faster version (closed form) and a
    simpler version separately when they differ.
  - with two candidate programs for one task, a proved helper found in one is
    generalised and reused in the other in a later cycle, with its schema proof.
  - running AIOC twice with the same seed and budget produces identical
    reports.

### 4.10 Piglog2 — Neuroprolog grouping (optional mode)

- R4.10.1 Group goals into concurrent and non-concurrent groups using data
  dependencies, purity, determinism and declared or *static* costs. Goals are
  never executed during conversion.
- R4.10.2 Only goals proved deterministic (or `once`-equivalent) may enter a
  concurrent group.
- R4.10.3 The suite's own declarations (`piglog_cost/2` etc.) are consumed by
  the converter and not copied into generated code.
- Acceptance [regression]: a nondeterministic goal after `member/2` is never
  wrapped in `concurrent/3`; the README example converts without errors.

---

## 5. MNN, AMNN and ANN generation

- R5.1 `make_mnn(Source, Options, Bundle)`: runs the chain under AIOC and writes the bundle
  (§8).
- R5.2 `make_amnn(MNN, Domain, AMNN, Proof)`: compiles an MNN into a network:
  - each predicate becomes a layer group; each clause a neuron set;
  - guards become threshold neurons, arithmetic becomes linear neurons with
    fixed weights, list traversal becomes a recurrent cell with explicit state;
  - weights are derived (not trained) and each weight's origin (clause, goal)
    is recorded;
  - equivalence with the MNN is proved on the declared finite or discretised
    domain (by structural proof, or by exhaustive check where the domain is
    finite and small enough; the method is named in the proof).
- R5.3 `make_ann(MNN, TrainingDomain, Options, ANN, Report)`:
  - a plain weighted network (layers, activations, weights as rationals or
    floats, chosen by option), trained deterministically from a seed;
  - training uses **manual gradient descent** (§6);
  - the report gives error on training data and on held-out data, and the ANN
    is labelled `approximate` unless verified exhaustively on a finite domain.
- R5.4 `run_net(Net, Input, Output, Trace)`: forward pass with per-neuron trace.
- R5.5 Networks are stored as Prolog data terms and can be printed as tables.

---

## 6. Manual gradient descent

- R6.1 Symbolic differentiation of the network's loss with respect to each
  weight, producing a readable gradient expression per weight.
- R6.2 `gd_step(Net, Batch, LearningRate, Net1, StepTrace)`: one update with
  every weight's old value, gradient, new value.
- R6.3 Users can step, pause, edit a weight and resume; the edit is recorded in
  the trace.
- R6.4 Deterministic: same seed and data give the same weights.

---

## 7. Proof system

- R7.1 Proof steps: `proof_step(Id, Rule, Premises, Conclusion)`.
- R7.2 Rule library (each rule has a documented soundness argument in
  `docs/proof_rules.md`):
  - unfold / fold (with fold-safety conditions);
  - clause and goal reordering under purity and determinism conditions;
  - definition introduction (for memoisation and hoisting);
  - findall-to-fold over finite generators;
  - structural and well-founded induction (from §4.3 measures);
  - algebraic identity (polynomial and rational identities decided by
    normalisation);
  - guard exhaustiveness and exclusivity (for cut removal);
  - finite-domain exhaustion (for AMNN and small domains), with the domain
    listed in the proof.
- R7.3 Every proof states its **domain and modes**; equivalence outside them is
  not claimed.
- R7.4 Each MNN bundle includes the machine proof (`Name.proof.pl`) and a
  rendered proof (`Name.proof.md`) a reader can follow step by step.
- R7.5 A rewrite without a checked proof is not applied (the predicate is kept
  and the reason recorded).

---

## 8. MNN bundle (output)

For an MNN named `Name`, write to an output directory:

| File | Contents |
| --- | --- |
| `Name.pl` | The MNN: standalone, loadable Prolog |
| `Name.original.pl` | The original algorithm (or S2A-synthesised algorithm) |
| `Name.proof.pl` | Machine-checkable proof terms |
| `Name.proof.md` | Human-readable proof |
| `Name.trace.pl` | Stage events, quantum-inspired search history |
| `Name.report.md` | What changed, costs before/after, what was kept and why |
| `Name.amnn.pl`, `Name.ann.pl` | Present only when requested |

---

## 9. User interface

All commands run from the SWI-Prolog REPL:

```prolog
?- mnn(File, Query).                       % optimise, load, run Query
?- mnn(File, Query, Options).
?- mnn_compile(File, OutDir, Options).     % write the bundle
?- mnn_from_spec(Name, Spec, OutDir, Options).
?- mnn_amnn(Name, Domain, OutDir).
?- mnn_ann(Name, Domain, Options, OutDir).
?- mnn_check(OutDir, Name).                % re-check a bundle's proof
?- mnn_aioc(Sources, Options, Report).     % run AIOC cycles over candidates
?- mnn_neuroprolog(File, Query, Options).  % Neuroprolog mode
```

Options: `stages(List)`, `quantum(off|inspired)`, `show(code|trace|proof)`,
`domain(Types)`, `seed(N)`, `allow_table(Bool)`.

A command-line wrapper `bin/mnn` exposes the same commands.

---

## 10. Neuroprolog mode

- R10.1 Group predicates (§4.10); assign each group an executor: the MNN, its
  AMNN, or its ANN, chosen per group by option or by default (AMNN when proved,
  else MNN).
- R10.2 A deterministic coordinator runs concurrent groups with
  `concurrent/3` and sequential groups in order, and merges results.
- R10.3 The trace shows which executor produced each intermediate value.
- R10.4 Any ANN-executed group marks the final answer `approximate`.

---

## 11. MNN chatbot

- R11.1 Record utterances as ordered events with source text (as MNN2).
- R11.2 Supported patterns at minimum: ownership, property, location
  composition, employment changes with corrections, simple rules
  ("A premium customer receives free shipping").
- R11.3 Each answer is computed by an MNN from the library and returns
  `answer`, `evidence`, `trace` separately; unsupported questions get an
  explicit `unsupported` answer, never a guess.
- R11.4 Optional web interface (SWI-Prolog `http` libraries, localhost only).

---

## 12. MNN agent

- R12.1 Plans projects and writes text artifacts only inside a configured
  workspace (as MNN3): no absolute paths, no traversal, size limits.
- R12.2 Uses MNNs for decomposition and ordering steps; each plan step cites the
  MNN and proof used.
- R12.3 Never executes generated code outside the suite's sandboxed module
  runner; never uses shell, sockets, HTTP clients or foreign libraries.
- R12.4 Default-deny capability monitor; security tests run first in CI.

---

## 13. Benchmarks and evaluation

- R13.1 Corpus: the regression programs above, the MNN1 task families
  (sequence, numeric, time series, ranking, rule chains, composition), and the
  8,900-case benchmark archive from MNN1 once adapted.
- R13.2 Protocol: fixed train/held-out splits; the expected answer is never
  passed to the system under test (fixing the leakage noted in MNN1's
  benchmark notes).
- R13.3 Compare classical MNN, quantum-inspired MNN, AMNN, ANN, and (when
  provided) an external NN baseline: accuracy, time, size, proof size.
- R13.4 Results are reported as measured, including null and negative results.

---

## 14. Repository structure

```
prolog/
  ir/            parse, emit, normalise
  s2a/  starlog/  pid/  loop2/  detlog/  plop/  algebraplop/
  quantum/       qi_search, qi_export
  proof/         rules, checker (independent), render
  aioc/          incorporate (front ends), simplify, assess, allocate, cycle, library
  nets/          amnn, ann, manual_gd, run_net
  neuroprolog/   grouping (piglog2), coordinator
  chatbot/  agent/  core/ (MNN1-style facts and traces)
bin/mnn
tests/           unit, integration, regression, proof, security
benchmarks/
docs/            proof_rules.md, ir.md, each part's guide
examples/
PROGRAM_REQUIREMENTS.md  PROGRESS.md  README.md  LICENSE
```

---

## 15. Agent instructions

For every stage the agent must:

1. read these requirements and `PROGRESS.md`;
2. implement only the stage's scope;
3. add unit, integration, regression and proof tests;
4. run `swipl -q -s tests/run.pl` and fix failures until all pass;
5. run the proof checker over every bundle in `examples/`;
6. update documentation and `PROGRESS.md` (done, limitations, open questions).

The agent must not:

- claim a proof that `check_proof/4` has not accepted;
- describe tested behaviour as proved;
- weaken, skip or delete a failing test to make the suite pass;
- leave stubs that return success; an unimplemented feature must return
  `unavailable(Reason)`;
- load code from the original repositories at run time;
- execute user goals during conversion (except inside the sandboxed test
  runner, on explicit request);
- claim quantum hardware execution or quantum advantage;
- commit generated reports, summaries or scratch files to the repository root.

When a requirement is ambiguous, choose the behaviour that preserves the
original program's meaning, record the choice in `PROGRESS.md`, and open an
issue if it changes a public interface.

---

## 16. Implementation stages

| Stage | Deliver | Acceptance |
| --- | --- | --- |
| 1 | IR, parser, emitter, sandboxed runner, test harness, CI | Round-trip on corpus; R3.1–R3.4 |
| 2 | Proof term format, independent checker, unfold/fold and reordering rules, proof rendering | Hand-written proofs check; bad proofs rejected |
| 3 | PID measures and induction obligations | §4.3 acceptance |
| 4 | loop2 | §4.4 acceptance, with proofs |
| 5 | Detlog | §4.5 acceptance, with proofs |
| 6 | PLOp stages and proved closed forms | §4.6 acceptance |
| 7 | AlgebraPLOp | §4.7 acceptance |
| 8 | S2A and Starlog | §§4.1–4.2 acceptance |
| 9 | AIOC incorporate front ends (decision trees, CFGs), simplify, assess, bundle writer, library, REPL commands | §§4.9 (R4.9.2–R4.9.12, R4.9.20), 8–9; `mnn_check/2` passes on examples |
| 10 | Quantum-inspired search and export; AIOC allocation and cycle interaction | §4.8; §4.9 (R4.9.13–R4.9.19) |
| 11 | AMNN, ANN, manual gradient descent | §§5–6 |
| 12 | Neuroprolog mode | §§4.10, 10 |
| 13 | Core, chatbot, agent | §§11–12 |
| 14 | Benchmarks | §13 report |

---

## 17. Definition of done

Version 1 is done when:

1. Every regression test in §4 passes.
2. Every example bundle's proof is accepted by the independent checker.
3. No rewrite is applied without a checked proof; unproved predicates are kept
   and reported.
4. Generated MNNs are standalone, re-entrant and pass their tests in a fresh
   process.
5. AMNNs are issued only with an equivalence proof on a stated domain; ANNs are
   labelled approximate with measured error.
6. Quantum-inspired features are classical, reproducible and labelled as such.
7. The chatbot and agent use library MNNs and return evidence and traces.
8. Benchmarks run under the leakage-free protocol and report results as
   measured.
9. AIOC runs all six stages, keeps faster and simpler versions separately,
   records assessments and allocations, and transfers only proved structures
   between candidates.
10. `README.md` explains MNN, AMNN, ANN, AIOC, the chain, the proof standard and the
   limits; `PROGRESS.md` records what remains.

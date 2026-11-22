# The Riemann ceiling

`prolog/riemann/riemann.pl` builds the manual neuronet that the Riemann
hypothesis (RH) is about. It compares three ways of choosing its weights:
by hand, by training, and optimally.

## The net

Neuron *k* is the sawtooth f_k(t) = {1/(k t)}, the fractional part of
1/(k t). The net has to learn χ(t), which is 1 on (0, 1) and 0 after that.
With weights c_1..c_N, the squared error is

    E(c) = ∫₀^∞ (χ − Σ c_k f_k)² dt = 1 − 2 c·b + c·G·c

where b_k = (1 − γ + ln k)/k and G is the Gram matrix of the neurons.
G is computed exactly by Vasyunin's cotangent-sum formula (`rh_gram/3`).

**Nyman–Beurling–Báez-Duarte criterion:** RH is true if and only if the best
error d_N² = 1 − b·G⁻¹·b tends to 0 as N → ∞.

**Burnol (unconditional):** d_N² ≥ (C0 + o(1)) / ln N, where
C0 = 2 + γ − ln 4π ≈ 0.046191.

**Báez-Duarte conjecture (assuming RH):** d_N² ~ C0 / ln N.

## The consequence

Assume RH and the conjecture. Then the error of any net built from these
neurons falls only like 1/ln N, so halving the error d takes about N⁴
neurons. That limit is the same whether a person writes the weights down
or an optimiser finds them: no choice of weights can beat d_N². Getting
past it takes a new basis (a new idea), not more neurons or more compute.

`rh_neurons_needed/2` turns this into numbers:
- d² = 0.01 needs about 10² neurons;
- d² = 0.001 needs about 10²⁰ neurons.

## Predicates

| Predicate | What it does |
| --- | --- |
| `rh_report(N, R)` | Gives the optimal, manual (Möbius, c_k = −μ(k)) and trained (10 steepest-descent steps) errors, d_N² ln N, C0/ln N, the ratio of d_N² to C0/ln N, and a proof term |
| `rh_check_proof(R, V)` | Recomputes the report independently and gives `accepted` or `rejected` |
| `rh_train(N, Steps, R)` | Gives the error after each exact line-search descent step from the Möbius weights |
| `rh_optimal_net/2`, `rh_manual_net/2`, `rh_error/3` | The three nets and the error of any weights |
| `rh_mobius_identity(M, P)` | Checks Σ_{k≤m} μ(k)⌊m/k⌋ = 1 exactly for 1 ≤ m ≤ M |
| `rh_robin(Lo, Hi, R)` | Checks Robin's inequality σ(n) < e^γ n ln ln n on a range (RH holds iff no n > 5040 breaks it) |

## Proof steps in a report

1. **`gram_positive_definite`:** the Cholesky pivots are all positive, so
   the optimum exists and is unique.
2. **`normal_equations`:** max |G c* − b| < 1e-9.
3. and 4. **`pythagoras`:** E(c) = d_N² + (c − c*)·G·(c − c*) holds for
   the manual and trained weights. The extra term is ≥ 0, so neither set
   of weights can be better than the optimum.
5. **`descent`:** each training step lowers the error.
6. **`mobius_identity`:** the integer identity behind the manual weights.

## Results so far

| N | optimal d_N² | manual | trained (10 steps) | d_N² / (C0/ln N) |
| --- | --- | --- | --- | --- |
| 5 | 0.036102 | 0.048576 | 0.037655 | 1.258 |
| 10 | 0.023772 | 0.137186 | 0.036493 | 1.185 |
| 20 | 0.016504 | 0.099890 | 0.039277 | 1.070 |
| 30 | 0.014530 | 0.071221 | 0.037320 | 1.070 |

The ratio comes down toward 1 from above, which fits both Burnol's bound
and the conjecture. The Möbius weights a number theorist would write down
stay well above the optimum. Ten steps of descent close most of the gap but
not all of it, because G is badly conditioned.

## What is not proved

This module does not prove RH or the conjecture. Its checks run on finite
ranges, and the numbers are floats, rounded to 6 places in reports. The
claim about people and AI is a reading of the conjecture, not a theorem.

Tests: `swipl -q -g "load_files('tests/riemann_tests.pl'), run_tests(mnn_riemann), halt"`

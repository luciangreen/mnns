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

## Arbitrary precision (`riemann_hp.pl`)

`rh_hp_report(N, P, R)` is the same report computed with fixed-point big
integers at P decimal digits, with 10 guard digits. The constants are
computed rather than looked up: π by Machin's formula, ln by atanh
series, γ by Brent–McMillan, and cot by Taylor series. The result adds
`optimal_d2_digits` and `ratio_digits` atoms and a seventh proof step: for
N ≤ 120 it must agree with the float computation to 1e-9.
`rh_hp_check_proof/2` recomputes the report and compares.
`rh_hp_series/3` gives one row per N. `rh_hp_constant/3` gives π, γ, ln 2,
ln 2π or C0 to P digits.

The tests check the N = 10, 100 and 200 results digit for digit against an
independent Python mirror of the same algorithm. N = 100 at 40 digits takes
about 0.9 s. The work grows like N³.

Running it at 40 digits gives the same first 40 digits as running it at
60, and doubles agree with it to about 1e-14 up to N = 500. So floats were
not the bottleneck, and the big integers serve as a certificate.

| N | optimal d_N² | manual | trained | C0/ln N | ratio |
| --- | --- | --- | --- | --- | --- |
| 50 | 0.011869 | 0.058864 | 0.034913 | 0.011808 | 1.0052 |
| 100 | 0.010189 | 0.147298 | 0.043852 | 0.010030 | 1.0158 |
| 200 | 0.008921 | 0.262160 | 0.062677 | 0.008718 | 1.0232 |
| 250 | 0.008243 | 0.041788 | 0.035995 | 0.008366 | 0.9853 |
| 300 | 0.007995 | 0.073869 | 0.038857 | 0.008098 | 0.9872 |
| 500 | 0.007420 | 0.075856 | 0.038318 | 0.007433 | 0.9983 |

d_300² = 0.007994899430921907469365107625 and
d_500² = 0.007419858011602131374781595266 (30 digits).

From N = 40 on, the ratio stays between 0.976 (its lowest, at N = 231) and
1.045 (at N = 94). It first drops below 1 at N = 41, and is below 1 for 260 of
N = 2..500. Burnol's bound is asymptotic, so values below 1 at finite N do
not contradict it. A ratio hovering near 1 is what the Báez-Duarte
conjecture predicts.

## What is not proved

This module does not prove RH or the conjecture. Its checks run on finite
ranges, and the numbers are floats, rounded to 6 places in reports. The
claim about people and AI is a reading of the conjecture, not a theorem.

An illustration brief for the graphs is in [`riemann_illustration.md`](riemann_illustration.md).

Tests: `swipl -q -g "load_files('tests/riemann_tests.pl'), run_tests(mnn_riemann), halt"`

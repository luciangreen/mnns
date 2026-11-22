# Illustration brief: the Riemann ceiling

A brief to paste into an image or chart tool such as ChatGPT. Every number
comes from `prolog/riemann/riemann.pl` and `riemann_hp.pl` (up to 30 digits
were checked; the tables round to 4).

---

## Context for the illustrator

The Riemann hypothesis (RH) is equivalent to a statement about a simple
neural net. Neuron k is the sawtooth wave f_k(t) = frac(1/(k·t)). The net
has to learn a step: 1 for 0 < t < 1, and 0 after that. RH holds if and
only if the best squared error d_N² of an N-neuron net goes to 0.

There is a floor of C0 / ln N, where C0 = 2 + γ − ln 4π ≈ 0.0462. Burnol
proved that errors cannot fall faster than this, asymptotically. Under RH,
Báez-Duarte conjectured that the best error follows the floor exactly.

The figures compare the floor with:
- **the optimum:** the best weights, solved exactly;
- **the human method:** hand-written Möbius weights, c_k = −μ(k);
- **the AI method:** 10 steps of gradient descent from the human weights.

The figures must not claim that RH is proved. They show computations
for N up to 500.

Style: a clean, modern mathematical figure on a white background with thin
lines, a sans-serif font, and labelled axes and legend. Use the same four
colours in every view:
- floor: dark grey, dashed;
- optimum: deep blue, solid, thickest line;
- human (Möbius): orange, thin and jagged, with small dots;
- AI (trained): green, solid.

---

## Figure 1: the main graph (floor vs optimum vs the two methods)

**Title:** "The Riemann ceiling: neurons vs error"

**Axes:**
- x-axis: number of neurons N, log scale from 1 to 500, with ticks at 1, 2,
  5, 10, 20, 50, 100, 200, 500.
- y-axis: squared error d², log scale from 0.005 to 4, with ticks at 0.005,
  0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 2.

**Data** (plot points and join them; the human line should zig-zag between
the listed points too, since it jumps with the Möbius function):

| N | optimum | human (Möbius) | AI (10 steps) | floor C0/ln N | optimum ÷ floor |
| --- | --- | --- | --- | --- | --- |
| 1 | 0.8582 | 3.1062 | 0.8582 | — | — |
| 2 | 0.2900 | 1.0762 | 0.2900 | 0.0666 | 4.351 |
| 3 | 0.0938 | 0.2144 | 0.0938 | 0.0420 | 2.232 |
| 5 | 0.0361 | 0.0486 | 0.0377 | 0.0287 | 1.258 |
| 8 | 0.0242 | 0.0374 | 0.0324 | 0.0222 | 1.088 |
| 10 | 0.0238 | 0.1372 | 0.0365 | 0.0201 | 1.185 |
| 15 | 0.0183 | 0.1065 | 0.0381 | 0.0171 | 1.075 |
| 20 | 0.0165 | 0.0999 | 0.0393 | 0.0154 | 1.070 |
| 30 | 0.0145 | 0.0712 | 0.0373 | 0.0136 | 1.070 |
| 41 | 0.0123 | 0.0652 | 0.0343 | 0.0124 | 0.991 |
| 50 | 0.0119 | 0.0589 | 0.0349 | 0.0118 | 1.005 |
| 60 | 0.0115 | 0.0547 | 0.0360 | 0.0113 | 1.017 |
| 80 | 0.0110 | 0.0960 | 0.0403 | 0.0105 | 1.042 |
| 100 | 0.0102 | 0.1473 | 0.0439 | 0.0100 | 1.016 |
| 150 | 0.0094 | 0.0704 | 0.0410 | 0.0092 | 1.018 |
| 200 | 0.0089 | 0.2622 | 0.0627 | 0.0087 | 1.023 |
| 231 | 0.0083 | 0.0574 | 0.0373 | 0.0085 | 0.976 |
| 250 | 0.0082 | 0.0418 | 0.0360 | 0.0084 | 0.985 |
| 300 | 0.0080 | 0.0739 | 0.0389 | 0.0081 | 0.987 |
| 400 | 0.0077 | 0.0674 | 0.0415 | 0.0077 | 1.000 |
| 500 | 0.0074 | 0.0759 | 0.0383 | 0.0074 | 0.998 |

**What the picture should show:**
- The blue optimum falls steeply at first. From about N = 40 it lies almost
  on top of the grey dashed floor and dips just below it in places.
- The orange human line stays well above the floor (5–30 times from N = 10) and jumps up and
  down. Its tallest spikes reach 0.26 at N = 200 and 0.147 at N = 100.
- The green AI line sits on a nearly flat plateau between 0.032 and 0.063
  from N ≈ 5 onwards. Training with ten descent steps does not reach the
  floor.
- Shade the region below the blue curve very lightly in blue, labelled "no
  weights can get here (proved for each N)".

**Annotations:**
- At N = 41, mark where blue first dips under the floor: "first dip below
  the floor".
- At N = 231: "lowest point: 0.976 × floor".
- A note near the right edge: "halving the error needs ~N⁴ neurons".

---

## Figure 2: how closely the optimum tracks the floor

A line plot of optimum ÷ floor (the last column above) against N, with the
x-axis log scale from 2 to 500 and the y-axis from 0.95 to 1.30. The y-axis
is cut at 1.30, so put the first values (4.35 at N = 2, 2.23 at N = 3) in an
inset or as an arrow pointing up.

- Draw a horizontal reference line at 1.0, labelled "Báez-Duarte
  conjecture: ratio → 1".
- The curve falls toward 1, then wobbles in a narrow band between 0.976 and
  1.045 from N = 40 to 500. It is below 1 for 260 of the 499 values of N.
- Caption: "The best possible net hugs the C0/ln N floor."

---

## Figure 3: the neurons themselves

A plot with t from 0 to 3 on the x-axis and the function value from −0.2 to
1.5 on the y-axis.

- Three thin sawtooth neurons, frac(1/t), frac(1/(2t)) and frac(1/(3t)), in
  light grey. Each one oscillates faster and faster as t → 0 and falls
  smoothly toward 0 when t is large.
- The target: a black step at height 1 for 0 < t < 1, dropping to 0 at
  t = 1.
- The trained net for N = 10, in blue, at roughly these points:

| t | 0.05 | 0.2 | 0.5 | 0.8 | 0.95 | 1.05 | 1.5 | 3 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| net(t) | 1.00 | 1.19 | 1.00 | 0.95 | 0.95 | 0.008 | 0.006 | 0.003 |

- Optionally, the N = 100 net in a lighter blue, closer to the step: 0.97
  at t = 0.95 and 0.003 at t = 1.05.
- Caption: "Sawtooth neurons summed into a step: RH holds iff this can be
  made exact."

---

## Figure 4: what the floor costs

How many neurons are needed for a target squared error d², if the
conjecture holds (N = e^(C0/d²)). Use a bar chart or a line plot with a log
scale.

| target d² | neurons needed |
| --- | --- |
| 0.02 | ~10 |
| 0.01 | ~10² |
| 0.005 | ~10⁴ |
| 0.002 | ~10¹⁰ |
| 0.001 | ~10²⁰ |

Caption: "Scaling up stops paying off: a new idea is needed, not a bigger net."

---

## Figure 5: the proof pipeline

Seven connected boxes flowing left to right, each with a green tick:
1. Gram matrix positive definite (Cholesky)
2. normal equations solved
3. human weights ≥ optimum (Pythagoras)
4. AI weights ≥ optimum (Pythagoras)
5. every training step lowers the error
6. Möbius identity Σ μ(k)⌊m/k⌋ = 1
7. float and 30–40-digit results agree

Feeding in from the left: "π, γ, ln, cot computed to P digits".
Coming out on the right: "report + independent checker: accepted".

---

## Figure 6: Robin's inequality (a second RH test)

A scatter plot of σ(n) / (n ln ln n) for n = 3 to 10,000. The y-axis runs
from 0 to 2.0; clip the n = 3 and n = 4 values (14.2 and 5.4) with arrows.

- Draw a horizontal red line at e^γ ≈ 1.781.
- Highlight the 26 points on or above the line, all at n ≤ 5040: 3, 4, 5,
  6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72, 84, 120, 180, 240,
  360, 720, 840, 2520, 5040. The last one is n = 5040, at 1.791.
- After 5040, every point stays below the line; the highest is n = 7560
  at 1.740.
- Caption: "RH iff no point after 5040 ever crosses the line."

---

## Optional concept art

A dark-blue night sky with a glowing horizontal line representing the
floor. Two climbers are trying to descend to it: a human with chalk and
equations (orange) and a robot following a gradient (green). Both stop above
the line. Beneath the line it reads "the critical line ½ + it". There is no
text claiming a proof.

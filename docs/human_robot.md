# Human and robot intelligence: P vs NP and comparative advantage

Two MNNs model what humans and robots are each good at. Both report exact,
proof-carrying results.

## P vs NP (`prolog/complexity/complexity.pl`)

3-SAT is NP-complete. A solution, once found, can be checked in at most 3m
literal tests. No known algorithm finds one in polynomial time; whether
one exists is the P vs NP question.

| Role | Model | Cost |
| --- | --- | --- |
| Robot, brute force | tries assignments in order | up to 2ⁿ |
| Robot, MNN | DPLL: unit propagation plus backtracking | exponential worst case (unless P = NP) |
| Human insight | NP's guess: a certificate that only needs checking | ≤ 3m |
| Team | human fixes K variables, robot searches the rest | ≤ 2ⁿ⁻ᴷ, or fails if the guess was wrong |

On a planted instance the human's guess comes from the hidden solution;
on an unplanted one it is only a guess. `cx_report/6` proves the following:
- the planted solution is valid;
- everything found is sound;
- brute force and the MNN agree;
- brute force is complete on unsatisfiable instances (all 2ⁿ tried);
- verification is linear;
- the team stays within 2ⁿ⁻ᴷ.

It leaves `p_vs_np` explicitly `open`.

Example scaling at m ≈ 4.26n, seed 11, with the human fixing half the
variables (`cx_scaling/4`):

| n | brute | MNN nodes | verify | team |
| --- | --- | --- | --- | --- |
| 8 | 70 | 4 | 56 | 5 |
| 12 | 3398 | 14 | 70 | 54 |
| 16 | 59458 | 11 | 101 | 233 |

DPLL is fast on these planted instances, because planted instances are
known to be easy. The worst case is still exponential.

## Comparative advantage (`prolog/complexity/advantage.pl`)

Ricardo's model as scheduling. Each task takes the human H_J time units
and the robot R_J. Both work at once, and the team finishes at
max(human load, robot load).

`ca_report/4` compares these allocations:
- each working alone;
- absolute advantage (each task to whoever is faster);
- comparative advantage (sort by H/R and choose the best cut);
- the exhaustive optimum.

It proves:
- the optimum (all 2ᵀ assignments checked);
- that the team beats either working alone;
- an LP duality certificate, in exact rationals, that the comparative
  cut with one shared task is the optimum when tasks can be split;
- integer ≥ fractional;
- a rounding bound for the cut;
- Ricardo's gain when the robot is faster at every task.

Example (`ca_report(8, 5, robot_better, R)`): the robot is faster at all 8
tasks.

| Allocation | Makespan |
| --- | --- |
| robot alone | 26 |
| absolute advantage | 26 (the robot takes everything) |
| comparative advantage cut | 17 |
| optimal | 15 |
| fractional optimum | 103/7 ≈ 14.7, certified by weight 3/7 |

The team saves 11 time units by giving the human the tasks where the human
is least worse.

## How the two connect

Getting the exact whole-task optimum is NP-hard: with H_J = R_J it is
PARTITION. So the comparative-advantage cut is the fast human-style
heuristic, exhaustive search is the robot's exact method, and the gap
between them is a small instance of the P vs NP question.

## Not proved

These are models. Treating human insight as a correct guess is an
assumption, real humans are not NP oracles, and P vs NP remains open.

Tests:

```sh
swipl -q -g "load_files('tests/complexity_tests.pl'), run_tests(mnn_complexity), halt"
swipl -q -g "load_files('tests/advantage_tests.pl'), run_tests(mnn_advantage), halt"
```

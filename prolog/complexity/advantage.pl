:- module(mnn_advantage,
          [ ca_tasks/4,
            ca_makespan/3,
            ca_report/4
          ]).

/** <module> Comparative advantage between a human and a robot

Ricardo's comparative advantage as a scheduling MNN. There are T tasks;
task J takes the human H_J time units and the robot R_J. Each task goes to
one of them, both work at once, and the team finishes at the makespan
max(human load, robot load).

The allocations compared:

  * human alone, robot alone;
  * absolute advantage: each task to whoever is faster at it;
  * comparative advantage: sort the tasks by the ratio H_J / R_J (the
    human's opportunity cost) and give the first I to the human, choosing
    the best cut I. This is Ricardo's rule;
  * optimal: the best of all 2^T assignments, by exhaustion.

Proofs in the report, all exact (integers and rationals):

  1. optimal_exhaustive: every one of the 2^T assignments was checked.
  2. team_beats_solo: optimal =< min(human alone, robot alone).
  3. duality_certificate: if tasks may be split, the comparative-advantage
     cut with one task shared is optimal. The certificate is a weight L in
     [0, 1]: any split satisfies makespan >= L * human load +
     (1 - L) * robot load >= sum_J min(L * H_J, (1 - L) * R_J). With L taken
     from the shared task, that lower bound equals the cut's makespan T*,
     so nothing beats it (weak LP duality).
  4. integer_above_fractional: optimal >= T*.
  5. rounding_bound: the comparative-advantage cut is within the shared
     task's cost of T*, so comparative =< T* + max(H_I, R_I).
  6. ricardo: when the robot is faster at every task, the team still
     gains min(H, R) - optimal >= 0 time units by giving the human the
     tasks where the human's disadvantage is smallest.
  7. complexity: the whole-task problem is NP-hard. With H_J = R_J it
     is PARTITION, so exhaustion (or an oracle) is needed for the exact
     optimum unless P = NP; the cut is the fast approximation.
*/

:- use_module(library(lists)).

lcg(X, Y) :- Y is (1103515245 * X + 12345) mod 2147483648.

%! ca_tasks(+T, +Seed, +Mode, -Tasks) is det.
%  Tasks = [task(J, H, R), ...]. Mode random gives H, R in 1..9;
%  robot_better gives H in 2..10 and R in 1..H-1.
ca_tasks(T, Seed, Mode, Tasks) :- tasks_(1, T, Seed, Mode, Tasks).

tasks_(J, T, _, _, []) :- J > T, !.
tasks_(J, T, X0, Mode, [task(J, H, R) | Ts]) :-
    lcg(X0, X1), H0 is (X1 >> 16) mod 9 + 1,
    lcg(X1, X2), R0 is (X2 >> 16) mod 9 + 1,
    (   Mode == robot_better
    ->  H is H0 + 1, R is (R0 - 1) mod (H - 1) + 1
    ;   H = H0, R = R0
    ),
    J1 is J + 1,
    tasks_(J1, T, X2, Mode, Ts).

%! ca_makespan(+Tasks, +Assignment, -Makespan) is det.
%  Assignment lists human or robot for each task.
ca_makespan(Ts, As, M) :- loads(Ts, As, 0, 0, H, R), M is max(H, R).

loads([], [], H, R, H, R).
loads([task(_, Hj, Rj) | Ts], [A | As], H0, R0, H, R) :-
    (   A == human -> H1 is H0 + Hj, R1 = R0 ; H1 = H0, R1 is R0 + Rj ),
    loads(Ts, As, H1, R1, H, R).

% ---- Allocations ----

absolute(Ts, As) :- maplist(faster, Ts, As).
faster(task(_, H, R), A) :- ( H < R -> A = human ; A = robot ).

by_ratio(Order, task(J1, H1, R1), task(J2, H2, R2)) :-
    X is H1 * R2, Y is H2 * R1,
    (   X < Y -> Order = (<)
    ;   X > Y -> Order = (>)
    ;   compare(Order, J1, J2)
    ).

% Best cut I in 0..T (first one if tied): the first I tasks in ratio order go to the human.
comparative(Ts, Sorted, M, Cut) :-
    length(Ts, T),
    numlist(0, T, Is),
    cut_makespans(Is, Ts, Sorted, Ms),
    min_list(Ms, M),
    nth0(Cut, Ms, M), !.

cut_makespans([], _, _, []).
cut_makespans([I | Is], Ts, Sorted, [M | Ms]) :-
    length(Pre, I), append(Pre, _, Sorted),
    findall(J, member(task(J, _, _), Pre), Js),
    cut_assign(Ts, Js, As),
    ca_makespan(Ts, As, M),
    cut_makespans(Is, Ts, Sorted, Ms).

cut_assign([], _, []).
cut_assign([task(J, _, _) | Ts], Js, [A | As]) :-
    ( memberchk(J, Js) -> A = human ; A = robot ),
    cut_assign(Ts, Js, As).

% Exhaustive: B = 0 .. 2^T - 1, bit K set means task K+1 goes to the human.
optimal(Ts, M, As, Tried) :-
    length(Ts, T), Tried is 1 << T, Last is Tried - 1,
    opt_(0, Last, T, Ts, none, M, As).

opt_(B, Last, _, _, best(M, As), M, As) :- B > Last, !.
opt_(B, Last, T, Ts, Best0, M, As) :-
    bits_assign(0, T, B, Asg),
    ca_makespan(Ts, Asg, Mk),
    (   Best0 = best(M0, _), M0 =< Mk -> Best1 = Best0 ; Best1 = best(Mk, Asg) ),
    B1 is B + 1,
    opt_(B1, Last, T, Ts, Best1, M, As).

bits_assign(K, T, _, []) :- K >= T, !.
bits_assign(K, T, B, [A | As]) :-
    ( (B >> K) /\ 1 =:= 1 -> A = human ; A = robot ),
    K1 is K + 1,
    bits_assign(K1, T, B, As).

% Fractional optimum along the ratio order: T*, the weight L and the shared task.
fractional(Sorted, TStar, L, task(J, H, R)) :-
    foldl([task(_, _, Rj), S0, S]>>(S is S0 + Rj), Sorted, 0, RAll),
    frac_(Sorted, 0, RAll, TStar, L, task(J, H, R)).

frac_([task(J, H, R) | Ts], Hp, Rs0, TStar, L, Split) :-
    Rs is Rs0 - R,
    F is (Rs + R - Hp) rdiv (H + R),
    (   F >= 0, F =< 1
    ->  TStar is Hp + F * H, L is R rdiv (H + R), Split = task(J, H, R)
    ;   Hp1 is Hp + H,
        frac_(Ts, Hp1, Rs, TStar, L, Split)
    ).

lower_bound([], _, LB, LB).
lower_bound([task(_, H, R) | Ts], L, LB0, LB) :-
    LB1 is LB0 + min(L * H, (1 - L) * R),
    lower_bound(Ts, L, LB1, LB).

% ---- The report ----

%! ca_report(+T, +Seed, +Mode, -Report) is det.
ca_report(T, Seed, Mode, Report) :-
    integer(T), T >= 1, T =< 16,
    ca_tasks(T, Seed, Mode, Ts),
    foldl([task(_, Hj, Rj), h(A0, B0), h(A1, B1)]>>(A1 is A0 + Hj, B1 is B0 + Rj), Ts, h(0, 0), h(HAll, RAll)),
    absolute(Ts, AbsAs), ca_makespan(Ts, AbsAs, Abs),
    predsort(by_ratio, Ts, Sorted),
    comparative(Ts, Sorted, Comp, Cut),
    optimal(Ts, Opt, OptAs, Tried),
    fractional(Sorted, TStar, L, task(SJ, SH, SR)),
    lower_bound(Ts, L, 0, LB),
    Gain is min(HAll, RAll) - Opt,
    (   forall(member(task(_, H, R), Ts), R < H) -> Better = yes ; Better = no ),
    proof_(Tried, Opt, HAll, RAll, TStar, LB, L, Comp, SH, SR, Better, Gain, Proof),
    Report = [ tasks(Ts), human_alone(HAll), robot_alone(RAll),
               absolute_advantage(Abs), comparative_advantage(Comp, cut(Cut)),
               optimal(Opt, OptAs), fractional_optimum(TStar, shared(SJ)),
               robot_faster_at_every_task(Better), gains_from_trade(Gain),
               Proof ].

proof_(Tried, Opt, HAll, RAll, TStar, LB, L, Comp, SH, SR, Better, Gain, proof(Steps)) :-
    P1 = proved(tried(Tried)),
    (   Opt =< min(HAll, RAll) -> P2 = proved ; P2 = failed ),
    (   LB =:= TStar, L >= 0, L =< 1 -> P3 = proved(weight(L)) ; P3 = failed ),
    (   Opt >= TStar -> P4 = proved ; P4 = failed ),
    Slack is max(SH, SR),
    (   Comp =< TStar + Slack -> P5 = proved(within(Slack)) ; P5 = failed ),
    (   Better == yes
    ->  ( Gain >= 0 -> P6 = proved(gain(Gain)) ; P6 = failed )
    ;   P6 = not_applicable(human_faster_somewhere)
    ),
    Steps = [ step(1, optimal_exhaustive, P1), step(2, team_beats_solo, P2),
              step(3, duality_certificate, P3), step(4, integer_above_fractional, P4),
              step(5, rounding_bound, P5), step(6, ricardo, P6),
              step(7, complexity, np_hard(partition)) ].

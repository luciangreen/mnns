:- module(mnn_complexity,
          [ cx_instance/5,
            cx_verify/3,
            cx_brute/5,
            cx_dpll/4,
            cx_report/6,
            cx_scaling/4
          ]).

/** <module> Human and robot intelligence through P vs NP

A model of human and robot problem solving on 3-SAT, the first problem
shown NP-complete (Cook-Levin).

NP is the class of problems whose solutions can be checked quickly:
a nondeterministic machine guesses a certificate and a deterministic one
verifies it in polynomial time. P is the class that can be solved
quickly. P = NP asks whether search can always be made as cheap as
guessing and checking. It is open.

The roles:

  * Robot, brute force: tries the assignments in order. Complete, and
    on an unsatisfiable instance it must try all 2^n.
  * Robot, MNN: the same search with proved MNN optimisations (unit
    propagation and backtracking, i.e. DPLL). It still takes exponential
    time in the worst case, unless P = NP.
  * Human insight: NP's guess. The human supplies the values of the first
    K variables; checking a full certificate costs at most 3m literal
    tests (cx_verify/3), which is linear.
  * Team: the human fixes K variables and the robot brute-forces the
    other n - K, which takes at most 2^(n-K) steps. When the guess is
    wrong the team finds nothing and the robot must search everything.

Instances come from a fixed linear congruential generator. A planted
instance hides an assignment that satisfies every clause, and the
human's guesses are its bits, so the model treats insight as correct.
On an unplanted instance the same bits are only a guess.

cx_report/6 returns step counts and a proof term:

  1. planted_ok: the planted assignment satisfies a planted instance.
  2. soundness: every assignment found passes the verifier.
  3. agreement: brute force and MNN search agree on satisfiability.
  4. completeness: on an unsatisfiable instance brute force tried all
     2^n assignments.
  5. verify_linear: verification took at most 3m literal tests.
  6. team_bound: the team took at most 2^(n-K) steps, and a team
     solution keeps the human's K values.
  7. p_vs_np: open. Nothing here decides it; the measured step counts
     only illustrate it.
*/

:- use_module(library(lists)).

lcg(X, Y) :- Y is (1103515245 * X + 12345) mod 2147483648.

%! cx_instance(+N, +M, +Seed, +Planted, -Inst) is det.
%  Inst = inst(Assignment, Clauses): the planted (or guessed) assignment as
%  a list of 0/1 for variables 1..N, and M clauses of 3 literals +-V.
cx_instance(N, M, Seed, Planted, inst(A, Cs)) :-
    gen_bits(N, Seed, X1, A),
    gen_clauses(M, N, X1, Planted, A, Cs).

gen_bits(0, X, X, []) :- !.
gen_bits(N, X0, X, [B | Bs]) :-
    lcg(X0, X1), B is (X1 >> 16) mod 2,
    N1 is N - 1, gen_bits(N1, X1, X, Bs).

gen_clauses(0, _, _, _, _, []) :- !.
gen_clauses(M, N, X0, Planted, A, [C | Cs]) :-
    gen_lits(3, N, X0, X1, C0),
    (   Planted == true, \+ clause_true(C0, A)
    ->  C0 = [L | Ls], L1 is -L, C = [L1 | Ls]
    ;   C = C0
    ),
    M1 is M - 1,
    gen_clauses(M1, N, X1, Planted, A, Cs).

gen_lits(0, _, X, X, []) :- !.
gen_lits(J, N, X0, X, [L | Ls]) :-
    lcg(X0, X1), V is (X1 >> 16) mod N + 1,
    lcg(X1, X2), S is (X2 >> 16) mod 2,
    (   S =:= 1 -> L = V ; L is -V ),
    J1 is J - 1,
    gen_lits(J1, N, X2, X, Ls).

lit_true(L, A) :-
    V is abs(L), nth1(V, A, B),
    (   L > 0 -> B == 1 ; B == 0 ).

clause_true(C, A) :- member(L, C), lit_true(L, A), !.

all_true([], _).
all_true([C | Cs], A) :- clause_true(C, A), all_true(Cs, A).

%! cx_verify(+Clauses, +Assignment, -Result) is det.
%  Result = ok(Steps) or rejected(Steps); Steps counts literal tests.
cx_verify(Cs, A, Result) :- verify_(Cs, A, 0, Result).

verify_([], _, S, ok(S)).
verify_([C | Cs], A, S0, Result) :-
    scan_clause(C, A, S0, S1, Found),
    (   Found == true
    ->  verify_(Cs, A, S1, Result)
    ;   Result = rejected(S1)
    ).

scan_clause([], _, S, S, false).
scan_clause([L | Ls], A, S0, S, Found) :-
    S1 is S0 + 1,
    (   lit_true(L, A)
    ->  S = S1, Found = true
    ;   scan_clause(Ls, A, S1, S, Found)
    ).

%! cx_brute(+Clauses, +N, +Fixed, -Found, -Steps) is det.
%  Tries the assignments Fixed ++ bits(I) for I = 0, 1, ...; Found is the
%  first that satisfies every clause, or none. Steps counts tries.
cx_brute(Cs, N, Fixed, Found, Steps) :-
    length(Fixed, K), Free is N - K,
    Total is 1 << Free,
    brute_(0, Total, Free, Fixed, Cs, Found, Steps).

brute_(I, Total, _, _, _, none, Total) :- I >= Total, !.
brute_(I, Total, Free, Fixed, Cs, Found, Steps) :-
    int_bits(Free, I, Bs),
    append(Fixed, Bs, A),
    (   all_true(Cs, A)
    ->  Found = A, Steps is I + 1
    ;   I1 is I + 1,
        brute_(I1, Total, Free, Fixed, Cs, Found, Steps)
    ).

int_bits(N, I, Bs) :- int_bits_(0, N, I, Bs).
int_bits_(J, N, _, []) :- J >= N, !.
int_bits_(J, N, I, [B | Bs]) :- B is (I >> J) /\ 1, J1 is J + 1, int_bits_(J1, N, I, Bs).

% ---- MNN search: DPLL ----

lit_val(L, A, Val) :-
    V is abs(L), nth1(V, A, B),
    (   B == u -> Val = u
    ;   L > 0 -> Val = B
    ;   Val is 1 - B
    ).

% propagate(+Cs, +A0, -A): unit propagation; fails on a conflict.
propagate(Cs, A0, A) :-
    scan_units(Cs, A0, none, Unit),
    (   Unit == none
    ->  A = A0
    ;   V is abs(Unit), (Unit > 0 -> B = 1 ; B = 0),
        set_nth1(V, A0, B, A1),
        propagate(Cs, A1, A)
    ).

% Fails if some clause is false; otherwise Unit is the first unit literal.
scan_units([], _, U, U).
scan_units([C | Cs], A, U0, U) :-
    lit_vals(C, A, Vals),
    (   memberchk(1, Vals)
    ->  U1 = U0
    ;   unassigned(C, Vals, Un),
        Un \== [],
        (   Un = [L], U0 == none -> U1 = L ; U1 = U0 )
    ),
    scan_units(Cs, A, U1, U).

lit_vals([], _, []).
lit_vals([L | Ls], A, [V | Vs]) :- lit_val(L, A, V), lit_vals(Ls, A, Vs).

unassigned([], [], []).
unassigned([L | Ls], [V | Vs], Un) :-
    (   V == u -> Un = [L | Un1] ; Un = Un1 ),
    unassigned(Ls, Vs, Un1).

set_nth1(1, [_ | T], X, [X | T]) :- !.
set_nth1(I, [H | T], X, [H | T1]) :- I1 is I - 1, set_nth1(I1, T, X, T1).

%! cx_dpll(+Clauses, +N, -Found, -Nodes) is det.
cx_dpll(Cs, N, Found, Nodes) :-
    length(A0, N), maplist(=(u), A0),
    dpll_(Cs, A0, 0, Nodes, Found).

dpll_(Cs, A0, Nd0, Nd, Found) :-
    Nd1 is Nd0 + 1,
    (   propagate(Cs, A0, A)
    ->  (   nth1(I, A, u)
        ->  set_nth1(I, A, 1, A1),
            dpll_(Cs, A1, Nd1, Nd2, F1),
            (   F1 \== none
            ->  Found = F1, Nd = Nd2
            ;   set_nth1(I, A, 0, A2),
                dpll_(Cs, A2, Nd2, Nd, Found)
            )
        ;   Found = A, Nd = Nd1
        )
    ;   Found = none, Nd = Nd1
    ).

% ---- The report ----

%! cx_report(+N, +M, +Seed, +Planted, +K, -Report) is det.
cx_report(N, M, Seed, Planted, K, Report) :-
    integer(N), N >= 1, integer(K), K >= 0, K =< N,
    cx_instance(N, M, Seed, Planted, inst(A0, Cs)),
    cx_brute(Cs, N, [], FB, SB),
    cx_dpll(Cs, N, FD, SD),
    length(Hint, K), append(Hint, _, A0),
    cx_brute(Cs, N, Hint, FT, ST),
    (   FB == none -> Sat = no, Verify = none
    ;   Sat = yes, cx_verify(Cs, FB, ok(VS)), Verify = VS
    ),
    (   FT == none -> Team = team(K, ST, failed) ; Team = team(K, ST, solved) ),
    proof_(N, M, Planted, Cs, A0, Hint, FB, SB, FD, FT, ST, K, Proof),
    Report = [ n(N), m(M), planted(Planted), sat(Sat),
               robot_brute(SB), robot_mnn(SD), human_verify(Verify),
               Team, Proof ].

proof_(N, M, Planted, Cs, A0, Hint, FB, SB, FD, FT, ST, K, proof(Steps)) :-
    (   Planted == true
    ->  ( all_true(Cs, A0) -> P1 = proved ; P1 = failed )
    ;   P1 = not_applicable(unplanted)
    ),
    (   sound(Cs, FB), sound(Cs, FD), sound(Cs, FT) -> P2 = proved ; P2 = failed ),
    (   ( FB == none, FD == none ; FB \== none, FD \== none ) -> P3 = proved ; P3 = failed ),
    (   FB == none
    ->  ( SB =:= 1 << N -> P4 = proved(tried_all(SB)) ; P4 = failed )
    ;   P4 = not_applicable(satisfiable)
    ),
    (   FB == none
    ->  P5 = not_applicable(no_certificate)
    ;   cx_verify(Cs, FB, ok(VS)), Max is 3 * M,
        ( VS =< Max -> P5 = proved(at_most(Max)) ; P5 = failed )
    ),
    Bound is 1 << (N - K),
    (   ST =< Bound, ( FT == none -> true ; append(Hint, _, FT) )
    ->  P6 = proved(at_most(Bound))
    ;   P6 = failed
    ),
    Steps = [ step(1, planted_ok, P1), step(2, soundness, P2),
              step(3, agreement, P3), step(4, completeness, P4),
              step(5, verify_linear, P5), step(6, team_bound, P6),
              step(7, p_vs_np, open) ].

sound(_, none) :- !.
sound(Cs, A) :- cx_verify(Cs, A, ok(_)).

%! cx_scaling(+MaxN, +Seed, +Planted, -Rows) is det.
%  row(N, M, Brute, MNN, Verify, Team) for N = 2, 4, ..., MaxN at the hard
%  clause ratio m = 4.26 n, with the human fixing half the variables.
cx_scaling(MaxN, Seed, Planted, Rows) :-
    findall(N, (between(1, MaxN, N), N mod 2 =:= 0), Ns),
    scaling_rows(Ns, Seed, Planted, Rows).

scaling_rows([], _, _, []).
scaling_rows([N | Ns], Seed, Planted, [row(N, M, SB, SD, V, ST) | Rows]) :-
    M is (426 * N + 50) // 100, K is N // 2,
    cx_report(N, M, Seed, Planted, K, R),
    memberchk(robot_brute(SB), R), memberchk(robot_mnn(SD), R),
    memberchk(human_verify(V), R), memberchk(team(_, ST, _), R),
    scaling_rows(Ns, Seed, Planted, Rows).

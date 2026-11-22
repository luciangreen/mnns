:- module(mnn_riemann_hp,
          [ rh_hp_constant/3,
            rh_hp_gram/4,
            rh_hp_report/3,
            rh_hp_check_proof/2,
            rh_hp_series/3
          ]).

/** <module> The Riemann ceiling in arbitrary precision

The same sawtooth net as mnn_riemann (see docs/riemann.md), computed with
fixed-point big integers instead of floats, so N can go well past 60 and
every digit asked for is trustworthy.

A real number x is held as the integer round-down(x * 10^W), where
W = P + 10 (P digits asked for, 10 guard digits). Every division is floor
division (div/2). The constants are computed, not looked up:

  * pi by Machin's formula 16 atan(1/5) - 4 atan(1/239);
  * ln 2 as 2 atanh(1/3), and ln x by halving x into [1, 2) and an
    atanh series of argument at most 1/3;
  * Euler's gamma by the Brent-McMillan algorithm;
  * cot(pi m / k) by Taylor series for sin and cos on (0, pi/2], with
    cot(pi - t) = -cot(t) for the rest.

The Gram matrix uses Vasyunin's formula exactly as in mnn_riemann; the
optimum comes from a fixed-point Cholesky solve with an integer square
root. rh_hp_report/3 gives the same fields and proof steps as
mnn_riemann:rh_report/2 at P digits, plus a seventh step: for N =< 120 the
optimum must agree with the float computation to 1e-9.

Tolerances in the proof are 10^-P. Results are still finite computations:
this does not prove RH or the Baez-Duarte conjecture.
*/

:- use_module(library(lists)).
:- use_module(riemann).

% ---- Fixed point ----

scale(P, W, S) :- W is P + 10, S is 10 ^ W.

isqrt(N, N) :- N < 2, !.
isqrt(N, R) :-
    X0 is 1 << (msb(N) // 2 + 1),
    isqrt_(N, X0, R).
isqrt_(N, X, R) :-
    X1 is (X + N div X) div 2,
    (   X1 >= X -> R = X ; isqrt_(N, X1, R) ).

atan_inv(N, S, X) :- T is S div N, N2 is N * N, atan_inv_(T, N2, 0, 0, X).
atan_inv_(0, _, _, X, X) :- !.
atan_inv_(T, N2, K, X0, X) :-
    Term is T div (2 * K + 1),
    (   K mod 2 =:= 0 -> X1 is X0 + Term ; X1 is X0 - Term ),
    T1 is T div N2, K1 is K + 1,
    atan_inv_(T1, N2, K1, X1, X).

% atanh(X) for 0 =< X =< S/3
atanh_fx(X, S, R) :- X2 is X * X div S, atanh_(X, X2, S, 0, 0, R).
atanh_(0, _, _, _, R, R) :- !.
atanh_(T, X2, S, K, R0, R) :-
    R1 is R0 + T div (2 * K + 1),
    T1 is T * X2 div S, K1 is K + 1,
    atanh_(T1, X2, S, K1, R1, R).

% ln of a fixed-point X > 0
log_fixed(X, S, Ln2, L) :-
    halve_into(X, S, 0, Y, E),
    Z is (Y - S) * S div (Y + S),
    atanh_fx(Z, S, At),
    L is E * Ln2 + 2 * At.

halve_into(Y0, S, E0, Y, E) :-
    (   Y0 >= 2 * S
    ->  Y1 is Y0 div 2, E1 is E0 + 1, halve_into(Y1, S, E1, Y, E)
    ;   Y0 < S
    ->  Y1 is Y0 * 2, E1 is E0 - 1, halve_into(Y1, S, E1, Y, E)
    ;   Y = Y0, E = E0
    ).

% ln of a positive integer K (exact reduction by its top power of 2)
log_int(K, S, Ln2, L) :-
    E is msb(K),
    Y is K * S div (1 << E),
    Z is (Y - S) * S div (Y + S),
    atanh_fx(Z, S, At),
    L is E * Ln2 + 2 * At.

% Brent-McMillan
euler_gamma(W, S, Ln2, G) :-
    N is (W * 2302585) div 4000000 + 2,
    log_int(N, S, Ln2, LogN),
    A is -LogN, N2 is N * N,
    bm_(1, A, S, N2, A, S, U, V),
    G is U * S div V.

bm_(_, 0, 0, _, U, V, U, V) :- !.
bm_(K, A0, B0, N2, U0, V0, U, V) :-
    B is B0 * N2 div (K * K),
    A is (A0 * N2 div K + B) div K,
    U1 is U0 + A, V1 is V0 + B, K1 is K + 1,
    bm_(K1, A, B, N2, U1, V1, U, V).

sincos(Th, S, Sin, Cos) :-
    X2 is Th * Th div S,
    sin_(Th, X2, S, 1, 0, Sin),
    cos_(S, X2, S, 1, 0, Cos).
sin_(0, _, _, _, R, R) :- !.
sin_(T, X2, S, I, R0, R) :-
    R1 is R0 + T,
    T1 is -T * X2 div S div ((2 * I) * (2 * I + 1)), I1 is I + 1,
    sin_(T1, X2, S, I1, R1, R).
cos_(0, _, _, _, R, R) :- !.
cos_(T, X2, S, I, R0, R) :-
    R1 is R0 + T,
    T1 is -T * X2 div S div ((2 * I - 1) * (2 * I)), I1 is I + 1,
    cos_(T1, X2, S, I1, R1, R).

% c(Cot1, ..., Cot(K-1)): cot(pi m / K) for m = 1..K-1
cot_table(K, S, Pi, Tab) :-
    H is (K - 1) // 2,
    numlist_or_empty(1, H, Ms),
    low_cots(Ms, K, S, Pi, Low),
    (   K mod 2 =:= 0, K > 1 -> Mid = [0] ; Mid = [] ),
    reverse(Low, RevLow),
    negate(RevLow, High),
    append([Low, Mid, High], All),
    compound_name_arguments(Tab, c, All).

low_cots([], _, _, _, []).
low_cots([M | Ms], K, S, Pi, [C | Cs]) :-
    Th is Pi * M div K,
    sincos(Th, S, Sin, Cos),
    C is Cos * S div Sin,
    low_cots(Ms, K, S, Pi, Cs).

negate([], []).
negate([X | Xs], [Y | Ys]) :- Y is -X, negate(Xs, Ys).

numlist_or_empty(L, H, []) :- H < L, !.
numlist_or_empty(L, H, Xs) :- numlist(L, H, Xs).

% ---- Context: constants and tables for N neurons at P digits ----

ctx(N, P, ctx(W, S, Ln2, Pi, Gamma, Log2Pi, Logs, Cots)) :-
    scale(P, W, S),
    S3 is S div 3, atanh_fx(S3, S, At3), Ln2 is 2 * At3,
    atan_inv(5, S, A5), atan_inv(239, S, A239), Pi is 16 * A5 - 4 * A239,
    euler_gamma(W, S, Ln2, Gamma),
    log_fixed(Pi, S, Ln2, LnPi), Log2Pi is Ln2 + LnPi,
    numlist(1, N, Ks),
    logs(Ks, S, Ln2, LogList), compound_name_arguments(Logs, l, LogList),
    cots(Ks, S, Pi, CotList), compound_name_arguments(Cots, t, CotList).

logs([], _, _, []).
logs([K | Ks], S, Ln2, [L | Ls]) :- log_int(K, S, Ln2, L), logs(Ks, S, Ln2, Ls).

cots([], _, _, []).
cots([K | Ks], S, Pi, [T | Ts]) :- cot_table(K, S, Pi, T), cots(Ks, S, Pi, Ts).

%! rh_hp_constant(+Name, +P, -Digits) is det.
%  pi, gamma, ln2, log2pi or c0 to P decimal places, as an atom.
rh_hp_constant(Name, P, Digits) :-
    ctx(1, P, Ctx), Ctx = ctx(W, S, Ln2, Pi, Gamma, Log2Pi, _, _),
    (   Name == pi -> X = Pi
    ;   Name == gamma -> X = Gamma
    ;   Name == ln2 -> X = Ln2
    ;   Name == log2pi -> X = Log2Pi
    ;   Name == c0 -> c0_fx(Ctx, X)
    ),
    fx_atom(X, W, P, Digits).

c0_fx(ctx(_, S, Ln2, Pi, Gamma, _, _, _), C0) :-
    log_fixed(Pi, S, Ln2, LnPi),
    C0 is 2 * S + Gamma - 2 * Ln2 - LnPi.

% ---- Neurons ----

vas(H, K, Cots, V) :-
    (   K =:= 1
    ->  V = 0
    ;   arg(K, Cots, Tab),
        K1 is K - 1,
        vas_(1, K1, H, K, Tab, 0, Sum),
        V is Sum div K
    ).
vas_(M, K1, _, _, _, Sum, Sum) :- M > K1, !.
vas_(M, K1, H, K, Tab, Sum0, Sum) :-
    arg(M, Tab, C),
    Sum1 is Sum0 + ((M * H) mod K) * C,
    M1 is M + 1,
    vas_(M1, K1, H, K, Tab, Sum1, Sum).

gram(J, K, ctx(_, S, _, Pi, Gamma, Log2Pi, Logs, Cots), G) :-
    D is gcd(J, K), H is J // D, L is K // D,
    arg(H, Logs, LogH), arg(L, Logs, LogL),
    vas(H, L, Cots, V1), vas(L, H, Cots, V2),
    T1 is (Log2Pi - Gamma) * (H + L) div (2 * H * L),
    T2 is (L - H) * (LogH - LogL) div (2 * H * L),
    T3 is Pi * (V1 + V2) div S div (2 * H * L),
    G is (T1 + T2 - T3) div D.

target(K, ctx(_, S, _, _, Gamma, _, Logs, _), B) :-
    arg(K, Logs, LogK),
    B is (S - Gamma + LogK) div K.

%! rh_hp_gram(+J, +K, +P, -Digits) is det.
rh_hp_gram(J, K, P, Digits) :-
    N is max(J, K), ctx(N, P, Ctx), gram(J, K, Ctx, G),
    Ctx = ctx(W, _, _, _, _, _, _, _),
    fx_atom(G, W, P, Digits).

gram_matrix(Ks, Ctx, Rows) :- gram_rows(Ks, Ks, Ctx, Rows).
gram_rows([], _, _, []).
gram_rows([J | Js], Ks, Ctx, [Row | Rows]) :-
    gram_row(Ks, J, Ctx, Row), gram_rows(Js, Ks, Ctx, Rows).
gram_row([], _, _, []).
gram_row([K | Ks], J, Ctx, [X | Xs]) :- gram(J, K, Ctx, X), gram_row(Ks, J, Ctx, Xs).

targets([], _, []).
targets([K | Ks], Ctx, [B | Bs]) :- target(K, Ctx, B), targets(Ks, Ctx, Bs).

% ---- Fixed-point linear algebra ----

sumprod([], [], A, A).
sumprod([X | Xs], [Y | Ys], A0, A) :- A1 is A0 + X * Y, sumprod(Xs, Ys, A1, A).

dot(Xs, Ys, S, D) :- sumprod(Xs, Ys, 0, P), D is P div S.

mat_vec([], _, _, []).
mat_vec([Row | Rows], Xs, S, [Y | Ys]) :- dot(Row, Xs, S, Y), mat_vec(Rows, Xs, S, Ys).

vsub([], [], []).
vsub([X | Xs], [Y | Ys], [Z | Zs]) :- Z is X - Y, vsub(Xs, Ys, Zs).

split_last([X | Xs], Prefix, Last) :- split_last_(Xs, X, Prefix, Last).
split_last_([], X, [], X).
split_last_([Y | Ys], X, [X | P], Last) :- split_last_(Ys, Y, P, Last).

cholesky(A, S, L, Pivots) :- chol_rows(A, S, [], L, Pivots).
chol_rows([], _, Prev, Prev, []).
chol_rows([Ai | As], S, Prev, L, [Pv | Pvs]) :-
    chol_offdiag(Prev, Ai, S, [], Acc, Aii),
    dot(Acc, Acc, S, AA),
    Pv is Aii - AA,
    Pv > 0,
    PvS is Pv * S, isqrt(PvS, Lii),
    append(Acc, [Lii], Row),
    append(Prev, [Row], Prev1),
    chol_rows(As, S, Prev1, L, Pvs).

chol_offdiag([], [Aii | _], _, Acc, Acc, Aii).
chol_offdiag([Lj | Ljs], [Aij | Ais], S, Acc0, Acc, Aii) :-
    split_last(Lj, Prefix, Ljj),
    dot(Acc0, Prefix, S, D),
    Lij is (Aij - D) * S div Ljj,
    append(Acc0, [Lij], Acc1),
    chol_offdiag(Ljs, Ais, S, Acc1, Acc, Aii).

forward(L, B, S, Y) :- forward_(L, B, S, [], Y).
forward_([], [], _, Y, Y).
forward_([Row | Rows], [Bi | Bs], S, Y0, Y) :-
    split_last(Row, Prefix, Lii),
    dot(Prefix, Y0, S, D),
    Yi is (Bi - D) * S div Lii,
    append(Y0, [Yi], Y1),
    forward_(Rows, Bs, S, Y1, Y).

backward(L, Y, S, X) :-
    length(L, N),
    pad_rows(L, N, Full),
    transpose_(Full, U),
    reverse(U, U1),
    rev_prefix_rows(U1, 1, Rev),
    reverse(Y, RY),
    forward(Rev, RY, S, RX),
    reverse(RX, X).

rev_prefix_rows([], _, []).
rev_prefix_rows([Row | Rows], I, [R | Rs]) :-
    reverse(Row, RevRow), length(R, I), append(R, _, RevRow),
    I1 is I + 1, rev_prefix_rows(Rows, I1, Rs).

pad_rows([], _, []).
pad_rows([Row | Rows], N, [F | Fs]) :-
    length(Row, K), Z is N - K, length(Zs, Z),
    maplist(=(0), Zs), append(Row, Zs, F),
    pad_rows(Rows, N, Fs).

transpose_([], []).
transpose_([[] | _], []) :- !.
transpose_(Rows, [Col | Cols]) :-
    heads_tails(Rows, Col, Rests),
    transpose_(Rests, Cols).
heads_tails([], [], []).
heads_tails([[H | T] | Rows], [H | Hs], [T | Ts]) :- heads_tails(Rows, Hs, Ts).

error_(G, B, S, C, E) :-
    dot(C, B, S, CB), mat_vec(G, C, S, GC), dot(C, GC, S, Q),
    E is S - 2 * CB + Q.

manual_weights([], _, []).
manual_weights([K | Ks], S, [W | Ws]) :-
    rh_mobius(K, Mu), W is -Mu * S, manual_weights(Ks, S, Ws).

train(0, _, _, _, C, C, []) :- !.
train(T, G, B, S, C0, C, [E | Es]) :-
    mat_vec(G, C0, S, GC), vsub(GC, B, Grad),
    dot(Grad, Grad, S, GG),
    (   GG =:= 0
    ->  C1 = C0
    ;   mat_vec(G, Grad, S, GGrad), dot(Grad, GGrad, S, GGG),
        Al is GG * S div GGG,
        step(C0, Grad, Al, S, C1)
    ),
    error_(G, B, S, C1, E),
    T1 is T - 1,
    train(T1, G, B, S, C1, C, Es).

step([], [], _, _, []).
step([C | Cs], [G | Gs], Al, S, [D | Ds]) :- D is C - Al * G div S, step(Cs, Gs, Al, S, Ds).

% ---- Output ----

% X / 10^(W-6) rounded to the nearest whole number, as a float in millionths
r6(X, W, Y) :- D is 10 ^ (W - 6), Q is (2 * X + D) div (2 * D), Y is Q / 1000000.0.

% X to P decimal places (rounded down), as an atom such as '0.0237718655'
fx_atom(X, W, P, Atom) :-
    Q is X div 10 ^ (W - P),
    (   Q < 0 -> Sign = '-', Q1 is -Q ; Sign = '', Q1 = Q ),
    format(atom(Ds), '~d', [Q1]),
    atom_length(Ds, Len),
    (   Len =< P
    ->  Pad is P + 1 - Len, length(Zs, Pad), maplist(=('0'), Zs),
        atomic_list_concat(Zs, ZA), atom_concat(ZA, Ds, Ds1)
    ;   Ds1 = Ds
    ),
    atom_length(Ds1, Len1), IntLen is Len1 - P,
    sub_atom(Ds1, 0, IntLen, _, Int), sub_atom(Ds1, IntLen, P, 0, Frac),
    atomic_list_concat([Sign, Int, '.', Frac], Atom).

% ---- The report ----

%! rh_hp_report(+N, +P, -Report) is semidet.
%  The Riemann-ceiling report for N neurons at P decimal digits.
rh_hp_report(N, P, Report) :-
    integer(N), N >= 1, integer(P), P >= 8,
    ctx(N, P, Ctx), Ctx = ctx(W, S, _, _, _, _, Logs, _),
    numlist(1, N, Ks),
    gram_matrix(Ks, Ctx, G), targets(Ks, Ctx, B),
    cholesky(G, S, L, Pivots),
    forward(L, B, S, Y), backward(L, Y, S, CStar),
    dot(B, CStar, S, BC), D2 is S - BC,
    manual_weights(Ks, S, CM),
    error_(G, B, S, CM, EM),
    train(10, G, B, S, CM, CT, TrainEs),
    last([EM | TrainEs], ET),
    c0_fx(Ctx, C0),
    Tol is 10 ^ (W - P),
    proof_(N, G, B, S, Tol, CStar, D2, Pivots, CM, CT, [EM | TrainEs], Proof),
    (   N >= 2
    ->  arg(N, Logs, LnN),
        D2Ln is D2 * LnN div S, Ceil is C0 * S div LnN,
        Ratio is D2 * LnN div C0,
        r6(D2Ln, W, D2Lnr), r6(Ceil, W, Ceilr), r6(Ratio, W, Ratior),
        fx_atom(Ratio, W, P, RatioDigits),
        Ceiling = [d2_times_ln_n(D2Lnr), c0_over_ln_n(Ceilr),
                   ratio_to_ceiling(Ratior), ratio_digits(RatioDigits)]
    ;   Ceiling = [d2_times_ln_n(undefined), c0_over_ln_n(undefined),
                   ratio_to_ceiling(undefined), ratio_digits(undefined)]
    ),
    r6(D2, W, D2r), r6(EM, W, EMr), r6(ET, W, ETr), r6(C0, W, C0r),
    fx_atom(D2, W, P, D2Digits),
    append([[n(N), digits(P), optimal_d2(D2r), optimal_d2_digits(D2Digits),
             manual_d2(EMr), trained_d2(ETr), c0(C0r)],
            Ceiling,
            [proof(Proof)]], Report).

proof_(N, G, B, S, Tol, CStar, D2, Pivots, CM, CT, Es, proof(Steps)) :-
    min_list(Pivots, MinPivot),
    mat_vec(G, CStar, S, GC), vsub(GC, B, Res),
    max_abs(Res, MaxRes),
    pythagoras(G, B, S, Tol, CStar, D2, CM, PM),
    pythagoras(G, B, S, Tol, CStar, D2, CT, PT),
    descent(Es, Tol, PD),
    rh_mobius_identity(N, PI),
    float_check(N, D2, S, PF),
    (   MinPivot > 0 -> P1 = proved ; P1 = failed ),
    (   MaxRes =< Tol -> P2 = proved ; P2 = failed ),
    Steps = [ step(1, gram_positive_definite, P1),
              step(2, normal_equations, P2),
              step(3, pythagoras(manual), PM),
              step(4, pythagoras(trained), PT),
              step(5, descent, PD),
              step(6, mobius_identity, PI),
              step(7, float_cross_check, PF) ].

max_abs(Xs, M) :- max_abs_(Xs, 0, M).
max_abs_([], M, M).
max_abs_([X | Xs], M0, M) :- M1 is max(M0, abs(X)), max_abs_(Xs, M1, M).

pythagoras(G, B, S, Tol, CStar, D2, C, P) :-
    error_(G, B, S, C, E),
    vsub(C, CStar, Dc),
    mat_vec(G, Dc, S, GDc), dot(Dc, GDc, S, Gap),
    Slack is abs(E - D2 - Gap),
    (   Slack =< Tol, Gap >= -Tol
    ->  P = proved(not_below_optimum)
    ;   P = failed(slack(Slack))
    ).

descent(Es, Tol, P) :-
    (   append(_, [X, Y | _], Es), Y > X + Tol
    ->  P = counterexample(rose)
    ;   length(Es, L), St is L - 1, P = proved(monotone(St))
    ).

float_check(N, D2, S, P) :-
    (   N =< 120
    ->  rh_optimal_net(N, net(optimal, _, D2f)),
        Diff is abs(D2f - D2 / S),
        (   Diff =< 1.0e-9 -> P = proved(agrees(1.0e-9)) ; P = failed(differs(Diff)) )
    ;   P = not_applicable(n_above_120)
    ).

%! rh_hp_check_proof(+Report, -Verdict) is semidet.
rh_hp_check_proof(Report, Verdict) :-
    memberchk(n(N), Report), memberchk(digits(P), Report),
    memberchk(proof(proof(Steps)), Report),
    memberchk(optimal_d2_digits(Ds), Report),
    (   rh_hp_report(N, P, Again),
        memberchk(proof(proof(Steps1)), Again),
        memberchk(optimal_d2_digits(Ds1), Again),
        Steps == Steps1, Ds == Ds1,
        forall(member(step(_, _, St), Steps), acceptable(St))
    ->  Verdict = accepted
    ;   Verdict = rejected
    ).

acceptable(proved).
acceptable(proved(_)).
acceptable(not_applicable(_)).

%! rh_hp_series(+Ns, +P, -Rows) is semidet.
%  row(N, OptimalD2, ManualD2, TrainedD2, CeilingC0OverLnN, Ratio) per N.
rh_hp_series([], _, []).
rh_hp_series([N | Ns], P, [row(N, D2, EM, ET, Ceil, Ratio) | Rows]) :-
    rh_hp_report(N, P, R),
    memberchk(optimal_d2(D2), R), memberchk(manual_d2(EM), R),
    memberchk(trained_d2(ET), R), memberchk(c0_over_ln_n(Ceil), R),
    memberchk(ratio_to_ceiling(Ratio), R),
    rh_hp_series(Ns, P, Rows).

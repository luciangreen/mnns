:- module(mnn_riemann,
          [ rh_gram/3,
            rh_target/2,
            rh_mobius/2,
            rh_optimal_net/2,
            rh_manual_net/2,
            rh_error/3,
            rh_train/3,
            rh_report/2,
            rh_check_proof/2,
            rh_mobius_identity/2,
            rh_robin/3,
            rh_neurons_needed/2
          ]).

/** <module> The Riemann ceiling: a manual neuronet RH is about

The Nyman-Beurling-Baez-Duarte criterion says the Riemann hypothesis (RH)
is true if and only if a one-layer net of sawtooth neurons can learn the
constant 1 as well as one likes. Neuron k is f_k(t) = {1/(k t)}, the
fractional part of 1/(k t), for t > 0. The target is chi(t) = 1 for
0 < t < 1 and 0 otherwise. With weights c_1..c_N the squared error is

    E(c) = integral over t > 0 of (chi(t) - sum c_k f_k(t))^2 dt
         = 1 - 2 c.b + c.G.c

where b_k = <chi, f_k> = (1 - gamma + ln k) / k and G is the Gram matrix
of the neurons, given exactly by Vasyunin's formula (rh_gram/3). The best
error for N neurons is d_N^2 = 1 - b.G^-1.b, and

    RH  <=>  d_N -> 0 as N -> infinity.

Burnol proved, without assuming RH, that d_N^2 >= (C0 + o(1)) / ln N,
where C0 = 2 + gamma - ln(4 pi) ~= 0.0462. Baez-Duarte conjectured that,
under RH, d_N^2 ~ C0 / ln N. That is the Riemann ceiling: if RH holds,
error falls only like 1 / ln N, so halving the error d needs about N^4
neurons, whoever chooses the weights.

Three ways to choose the weights are compared here:

  * manual: c_k = -mu(k), the Mobius net a number theorist writes down
    from sum_{k =< m} mu(k) floor(m / k) = 1;
  * trained: steepest descent with exact line search from the manual
    weights, as an AI optimiser would do;
  * optimal: the least-squares weights from a Cholesky solve of G c = b.

Proofs. rh_report/2 returns a proof term and rh_check_proof/2 checks it
again independently:

  1. gram_positive_definite: the Cholesky factorisation has positive
     pivots, so G is positive definite and the optimum is unique.
  2. normal_equations: the residual max |G c - b| is below 1e-9.
  3. pythagoras: for any weights c, E(c) = d_N^2 + (c - c*).G.(c - c*),
     checked for the manual and trained weights. Since G is positive
     definite, no choice of weights, by hand or by training, can beat the
     optimum: manual >= optimal and trained >= optimal.
  4. descent: every training step lowers the error (it falls by
     (g.g)^2 / (g.G.g) >= 0 for gradient g = G c - b).
  5. mobius_identity: sum_{k =< m} mu(k) floor(m / k) = 1 for every
     1 =< m =< N, checked exactly in integers.

What is not proved: RH itself, or the conjecture d_N^2 ~ C0 / ln N. The
report shows d_N^2 ln N next to C0 so the conjecture can be watched, not
assumed. rh_robin/3 checks a second RH equivalent, Robin's inequality
sigma(n) < e^gamma n ln ln n for n > 5040, exhaustively on a finite range.

Floats in reports are rounded to 6 decimal places so outputs are stable.
*/

:- use_module(library(lists)).
:- use_module(library(apply)).

euler_gamma(0.5772156649015329).

c0(C0) :- euler_gamma(G), C0 is 2 + G - log(4 * pi).

r6(X, Y) :- Y is round(X * 1000000) / 1000000.0.

% ---- Number theory ----

%! rh_mobius(+N, -Mu) is det.
%  The Mobius function mu(N) for N >= 1.
rh_mobius(1, 1) :- !.
rh_mobius(N, Mu) :- integer(N), N > 1, mobius_(N, 2, 1, Mu).

mobius_(1, _, S, S) :- !.
mobius_(N, P, S, Mu) :-
    (   P * P > N
    ->  Mu is -S
    ;   N mod P =:= 0
    ->  N1 is N // P,
        (   N1 mod P =:= 0
        ->  Mu = 0
        ;   S1 is -S, P1 is P + 1, mobius_(N1, P1, S1, Mu)
        )
    ;   P1 is P + 1, mobius_(N, P1, S, Mu)
    ).

%! rh_mobius_identity(+M, -Result) is det.
%  Checks sum_{k =< m} mu(k) floor(m / k) = 1 for every 1 =< m =< M.
rh_mobius_identity(M, Result) :-
    numlist(1, M, Ks),
    maplist(rh_mobius, Ks, Mus),
    (   between(1, M, Mm),
        mobius_sum(Ks, Mus, Mm, 0, S),
        S =\= 1
    ->  Result = counterexample(Mm, S)
    ;   Result = proved(exhaustive(M))
    ).

mobius_sum([], [], _, S, S).
mobius_sum([K | Ks], [Mu | Mus], M, S0, S) :-
    (   K > M
    ->  S = S0
    ;   S1 is S0 + Mu * (M // K),
        mobius_sum(Ks, Mus, M, S1, S)
    ).

% ---- The neurons ----

% Vasyunin's cotangent sum V(h, k) = sum_{m=1}^{k-1} {m h / k} cot(pi m / k).
vasyunin(H, K, V) :-
    K1 is K - 1,
    numlist_or_empty(1, K1, Ms),
    foldl(f(H, K)/[M, A0, A]>>(A is A0 + ((M * H) mod K) / K / tan(pi * M / K)),
          Ms, 0.0, V).

numlist_or_empty(L, H, []) :- H < L, !.
numlist_or_empty(L, H, Xs) :- numlist(L, H, Xs).

%! rh_gram(+J, +K, -G) is det.
%  <f_J, f_K>, the inner product of two sawtooth neurons on (0, inf).
rh_gram(J, K, G) :-
    D is gcd(J, K), H is J // D, L is K // D,
    euler_gamma(Gm),
    vasyunin(H, L, V1), vasyunin(L, H, V2),
    G0 is (log(2 * pi) - Gm) / 2 * (1 / H + 1 / L)
          + (L - H) / (2 * H * L) * log(H / L)
          - pi / (2 * H * L) * (V1 + V2),
    G is G0 / D.

%! rh_target(+K, -B) is det.
%  <chi, f_K> = (1 - gamma + ln K) / K.
rh_target(K, B) :- euler_gamma(G), B is (1 - G + log(K)) / K.

gram_matrix(N, Rows) :-
    numlist(1, N, Ks),
    maplist(f(Ks)/[J, Row]>>maplist(f(J)/[K, X]>>rh_gram(J, K, X), Ks, Row), Ks, Rows).

target_vector(N, Bs) :- numlist(1, N, Ks), maplist(rh_target, Ks, Bs).

% ---- Linear algebra on lists ----

dot(Xs, Ys, D) :- foldl([X, Y, A0, A]>>(A is A0 + X * Y), Xs, Ys, 0.0, D).

mat_vec(Rows, Xs, Ys) :- maplist(f(Xs)/[Row, Y]>>dot(Row, Xs, Y), Rows, Ys).

quad(G, Xs, Q) :- mat_vec(G, Xs, Ys), dot(Xs, Ys, Q).

vsub(Xs, Ys, Zs) :- maplist([X, Y, Z]>>(Z is X - Y), Xs, Ys, Zs).

vscale_sub(Xs, A, Ys, Zs) :- maplist(f(A)/[X, Y, Z]>>(Z is X - A * Y), Xs, Ys, Zs).

% cholesky(+A, -L, -Pivots): A = L L^T; row I of L has I entries.
% Fails if a pivot is not positive (A is not positive definite).
cholesky(A, L, Pivots) :- chol_rows(A, [], L, Pivots).

chol_rows([], Prev, Prev, []).
chol_rows([Ai | As], Prev, L, [S | Ss]) :-
    chol_offdiag(Prev, Ai, [], Acc, Aii),
    dot(Acc, Acc, AA),
    S is Aii - AA,
    S > 0,
    Lii is sqrt(S),
    append(Acc, [Lii], Row),
    append(Prev, [Row], Prev1),
    chol_rows(As, Prev1, L, Ss).

% Walks the earlier rows Lj with the matching entries Aij of row Ai;
% leaves the diagonal entry Aii.
chol_offdiag([], [Aii | _], Acc, Acc, Aii).
chol_offdiag([Lj | Ljs], [Aij | Ais], Acc0, Acc, Aii) :-
    split_last(Lj, Prefix, Ljj),
    dot(Acc0, Prefix, D),
    Lij is (Aij - D) / Ljj,
    append(Acc0, [Lij], Acc1),
    chol_offdiag(Ljs, Ais, Acc1, Acc, Aii).

% split_last(+List, -Prefix, -Last): deterministic.
split_last([X | Xs], Prefix, Last) :- split_last_(Xs, X, Prefix, Last).
split_last_([], X, [], X).
split_last_([Y | Ys], X, [X | P], Last) :- split_last_(Ys, Y, P, Last).

% forward(+L, +B, -Y): solves L Y = B for lower-triangular L (ragged rows).
forward(L, B, Y) :- forward_(L, B, [], Y).
forward_([], [], Y, Y).
forward_([Row | Rows], [Bi | Bs], Y0, Y) :-
    split_last(Row, Prefix, Lii),
    dot(Prefix, Y0, D),
    Yi is (Bi - D) / Lii,
    append(Y0, [Yi], Y1),
    forward_(Rows, Bs, Y1, Y).

% backward(+L, +Y, -X): solves L^T X = Y. Reversing rows and columns of
% L^T gives a lower-triangular matrix, so the forward solve is reused.
backward(L, Y, X) :-
    length(L, N),
    pad_rows(L, N, Full),
    transpose_(Full, U),
    reverse(U, U1),
    numlist(1, N, Is),
    maplist([Row, I, R]>>(reverse(Row, RevRow), length(R, I), append(R, _, RevRow)),
            U1, Is, Rev),
    reverse(Y, RY),
    forward(Rev, RY, RX),
    reverse(RX, X).

pad_rows(L, N, Full) :-
    maplist(f(N)/[Row, F]>>(length(Row, K), Z is N - K, length(Zs, Z),
                       maplist(=(0.0), Zs), append(Row, Zs, F)), L, Full).

transpose_([], []).
transpose_([[] | _], []) :- !.
transpose_(Rows, [Col | Cols]) :-
    maplist([[H | T], H, T]>>true, Rows, Col, Rests),
    transpose_(Rests, Cols).

% ---- The three nets ----

%! rh_error(+N, +Weights, -E) is det.
%  E(c) = 1 - 2 c.b + c.G.c for N neurons.
rh_error(N, C, E) :-
    gram_matrix(N, G), target_vector(N, B),
    error_(G, B, C, E).

error_(G, B, C, E) :- dot(C, B, CB), quad(G, C, Q), E is 1 - 2 * CB + Q.

%! rh_optimal_net(+N, -Net) is semidet.
%  Net = net(optimal, Weights, D2): the least-squares weights and d_N^2.
rh_optimal_net(N, net(optimal, C, D2)) :-
    gram_matrix(N, G), target_vector(N, B),
    optimal_(G, B, C, D2, _).

optimal_(G, B, C, D2, Pivots) :-
    cholesky(G, L, Pivots),
    forward(L, B, Y),
    backward(L, Y, C),
    dot(B, C, BC),
    D2 is 1 - BC.

%! rh_manual_net(+N, -Net) is det.
%  Net = net(manual, Weights, E): the Mobius weights c_k = -mu(k).
rh_manual_net(N, net(manual, C, E)) :-
    manual_weights(N, C),
    rh_error(N, C, E).

manual_weights(N, C) :-
    numlist(1, N, Ks),
    maplist([K, W]>>(rh_mobius(K, Mu), W is -float(Mu)), Ks, C).

%! rh_train(+N, +Steps, -Result) is semidet.
%  Steepest descent with exact line search from the manual weights.
%  Result = [errors(Es), final(E), optimal(D2), descent(Proof)] where Es
%  lists the error after 0..Steps steps (rounded).
rh_train(N, Steps, [errors(Es), final(EF), optimal(D2r), descent(P)]) :-
    gram_matrix(N, G), target_vector(N, B),
    optimal_(G, B, _, D2, _),
    manual_weights(N, C0),
    train_(Steps, G, B, C0, _, Raw),
    descent_check(Raw, P),
    maplist(r6, Raw, Es),
    last(Es, EF),
    r6(D2, D2r).

train_(Steps, G, B, C0, C, [E0 | Es]) :-
    error_(G, B, C0, E0),
    train_steps(Steps, G, B, C0, C, Es).

train_steps(0, _, _, C, C, []) :- !.
train_steps(S, G, B, C0, C, [E | Es]) :-
    descent_step(G, B, C0, C1),
    error_(G, B, C1, E),
    S1 is S - 1,
    train_steps(S1, G, B, C1, C, Es).

descent_step(G, B, C0, C1) :-
    mat_vec(G, C0, GC), vsub(GC, B, Grad),
    dot(Grad, Grad, GG),
    (   GG =:= 0
    ->  C1 = C0
    ;   quad(G, Grad, GGG),
        A is GG / GGG,
        vscale_sub(C0, A, Grad, C1)
    ).

descent_check(Es, P) :-
    (   append(_, [X, Y | _], Es), Y > X + 1.0e-12
    ->  P = counterexample(rose(X, Y))
    ;   length(Es, L), S is L - 1, P = proved(monotone(S))
    ).

% ---- The report and its proof ----

%! rh_report(+N, -Report) is semidet.
rh_report(N, Report) :-
    integer(N), N >= 1,
    gram_matrix(N, G), target_vector(N, B),
    optimal_(G, B, CStar, D2, Pivots),
    manual_weights(N, CM),
    error_(G, B, CM, EM),
    train_(10, G, B, CM, CT, TrainEs),
    last(TrainEs, ET),
    c0(C0),
    proof_(N, G, B, CStar, D2, Pivots, CM, CT, TrainEs, Proof),
    (   N >= 2
    ->  LnN is log(N), D2Ln is D2 * LnN, Ceil is C0 / LnN,
        Ratio is D2 / Ceil,
        maplist(r6, [D2Ln, Ceil, Ratio], [D2Lnr, Ceilr, Ratior]),
        Ceiling = [d2_times_ln_n(D2Lnr), c0_over_ln_n(Ceilr), ratio_to_ceiling(Ratior)]
    ;   Ceiling = [d2_times_ln_n(undefined), c0_over_ln_n(undefined), ratio_to_ceiling(undefined)]
    ),
    maplist(r6, [D2, EM, ET, C0], [D2r, EMr, ETr, C0r]),
    append([[n(N), optimal_d2(D2r), manual_d2(EMr), trained_d2(ETr), c0(C0r)],
            Ceiling,
            [proof(Proof)]], Report).

proof_(N, G, B, CStar, D2, Pivots, CM, CT, TrainEs, proof(Steps)) :-
    min_list(Pivots, MinPivot),
    mat_vec(G, CStar, GC), vsub(GC, B, Res),
    maplist([X, Y]>>(Y is abs(X)), Res, AbsRes), max_list(AbsRes, MaxRes),
    pythagoras(G, B, CStar, D2, CM, PM),
    pythagoras(G, B, CStar, D2, CT, PT),
    descent_check(TrainEs, PD),
    rh_mobius_identity(N, PI),
    (   MinPivot > 0 -> P1 = proved ; P1 = failed ),
    (   MaxRes < 1.0e-9 -> P2 = proved ; P2 = failed ),
    Steps = [ step(1, gram_positive_definite, P1),
              step(2, normal_equations, P2),
              step(3, pythagoras(manual), PM),
              step(4, pythagoras(trained), PT),
              step(5, descent, PD),
              step(6, mobius_identity, PI) ].

% E(c) - d^2 - (c - c*).G.(c - c*) = 0 and the gap is >= 0.
pythagoras(G, B, CStar, D2, C, P) :-
    error_(G, B, C, E),
    vsub(C, CStar, Dc),
    quad(G, Dc, Gap),
    Slack is abs(E - D2 - Gap),
    Tol is 1.0e-9 * max(1.0, abs(E)),
    (   Slack =< Tol, Gap >= -1.0e-12
    ->  P = proved(not_below_optimum)
    ;   P = failed(slack(Slack), gap(Gap))
    ).

%! rh_check_proof(+Report, -Verdict) is semidet.
%  Checks a report independently: recomputes the optimum for its N and
%  every proof step, and compares with the report.
rh_check_proof(Report, Verdict) :-
    memberchk(n(N), Report),
    memberchk(proof(proof(Steps)), Report),
    memberchk(optimal_d2(D2r), Report),
    (   rh_report(N, Again),
        memberchk(proof(proof(Steps1)), Again),
        memberchk(optimal_d2(D2r1), Again),
        Steps == Steps1,
        abs(D2r - D2r1) =< 1.0e-6,
        forall(member(step(_, _, S), Steps), proved_step(S))
    ->  Verdict = accepted
    ;   Verdict = rejected
    ).

proved_step(proved).
proved_step(proved(_)).

% ---- Robin's inequality ----

%! rh_robin(+Lo, +Hi, -Result) is det.
%  Checks sigma(n) < e^gamma n ln ln n for every Lo =< n =< Hi (n >= 3).
%  RH holds iff there is no exception above 5040. Result is
%  [checked(Count), exceptions(Ns), above_5040(Verdict)].
rh_robin(Lo0, Hi, [checked(Count), exceptions(Ex), above_5040(V)]) :-
    Lo is max(3, Lo0),
    (   Hi < Lo
    ->  Count = 0, Ex = []
    ;   Count is Hi - Lo + 1,
        numlist(Lo, Hi, Ns),
        include(robin_fails, Ns, Ex)
    ),
    (   member(X, Ex), X > 5040
    ->  V = counterexample(X)
    ;   V = none
    ).

robin_fails(N) :-
    sigma(N, S),
    euler_gamma(G),
    S >= exp(G) * N * log(log(N)).

sigma(N, S) :- sigma_(N, 2, 1, S).
sigma_(1, _, S, S) :- !.
sigma_(N, P, S0, S) :-
    (   P * P > N
    ->  S is S0 * (N + 1)
    ;   N mod P =:= 0
    ->  divide_out(N, P, 1, 1, N1, F),
        S1 is S0 * F, P1 is P + 1,
        sigma_(N1, P1, S1, S)
    ;   P1 is P + 1, sigma_(N, P1, S0, S)
    ).

% F = 1 + P + ... + P^e for the full power of P in N.
divide_out(N, P, Pk, F0, N1, F) :-
    (   N mod P =:= 0
    ->  N2 is N // P, Pk1 is Pk * P, F1 is F0 + Pk1,
        divide_out(N2, P, Pk1, F1, N1, F)
    ;   N1 = N, F = F0
    ).

% ---- How many neurons the ceiling asks for ----

%! rh_neurons_needed(+D2, -Log10N) is det.
%  Under the conjecture d_N^2 ~ C0 / ln N, the neurons needed for squared
%  error D2 are N = exp(C0 / D2); Log10N is log10 of that, rounded.
rh_neurons_needed(D2, Log10N) :-
    D2 > 0,
    c0(C0),
    L is C0 / D2 / log(10),
    r6(L, Log10N).

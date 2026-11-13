/*  s2a2_prover.pl -- the checker for mnns proof steps of rule edb_equivalence.

    A copy of S2A2's prolog/prover.pl (github.com/luciangreen/S2A2, commit cf72bda), with only the
    module name changed (prover -> mnn_edb_prover), so that mnns's proof checker can repeat
    the equivalence check without loading S2A2. S2A2's documentation follows.

    prover.pl -- checks that each stage's output is matched.

    Claims it can prove (each returns proved(How) or refuted(Counterexample)):

    1. net_reproduces(+NetFile, +Input, +Observed, -Result)
       The network, read ONLY through its weights (neuron/4, edge/3, recurrent/2),
       clamped with Input atoms, reaches a fixpoint where every Observed literal holds.
       Observed is a list of true(Atom) / false(Atom).

    2. program_reproduces(+Program, +Input, +Observed, -Result)
       The least model of Program plus Input satisfies every Observed literal.

    3. equivalent(+ProgA, +ProgB, +Targets, +EdbSpec, -Result)
       ProgA and ProgB compute the same Target relations for EVERY input:
         - proved(syntactic(Steps)) when B is A with duplicate or subsumed clauses or
           duplicate literals removed (theta-subsumption: sound for all domains);
         - proved(exhaustive(N)) when they agree on all N subsets of the input atoms
           built from EdbSpec = edb(Preds/Arity list, Constants);
         - refuted(input(Facts), only_in_a(As), only_in_b(Bs)) otherwise.

    Programs are lists of clauses (H :- B) or facts. Supported body goals: atoms,
    \+ Atom (stratified), X \= Y, X = Y, neq(X,Y).
*/
:- module(mnn_edb_prover, [net_reproduces/4, program_reproduces/4, equivalent/5,
                   least_model/3, read_program/2, net_forward/3,
                   net_matches_program/3, net_matches_program/4, net_equivalent_program/5, net_clauses/2]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(ordsets)).
:- use_module(library(yall)).

% ---------------------------------------------------------------- reading
read_program(File, Clauses) :-
    setup_call_cleanup(open(File, read, S),
                       read_all(S, Clauses), close(S)).
read_all(S, Cs) :-
    read_term(S, T, []),
    (   T == end_of_file -> Cs = []
    ;   T = (:- _) -> read_all(S, Cs)
    ;   findall(C, split_disjunction(T, C), Ts), append(Ts, Rest, Cs), read_all(S, Rest)
    ).

% (a ; b) in a body becomes two clauses, as pl2ann does
split_disjunction((H :- B), (H :- B1)) :- !, disj_body(B, B1).
split_disjunction(F, F).
disj_body((A ; B), X) :- !, ( disj_body(A, X) ; disj_body(B, X) ).
disj_body((A , B), (X , Y)) :- !, disj_body(A, X), disj_body(B, Y).
disj_body(G, G).

% ---------------------------------------------------------------- least model
clause_parts((H :- B), H, Gs) :- !, conj_list(B, Gs).
clause_parts(H, H, []).
conj_list((A, B), L) :- !, conj_list(A, LA), conj_list(B, LB), append(LA, LB, L).
conj_list(true, []) :- !.
conj_list(G, [G]).

pred_key(A, P/N) :- functor(A, P, N).

% stratum of each head predicate: s(p) >= s(q) for positive q, >= s(q)+1 for \+ q
strata(Clauses, Strata) :-
    findall(K, (member(C, Clauses), clause_parts(C, H, _), pred_key(H, K)), Ks0),
    sort(Ks0, Ks),
    findall(K-0, member(K, Ks), S0),
    length(Ks, NK), Lim is NK + 2,
    relax(Clauses, S0, Lim, Strata).
relax(_, S, 0, S) :- !.
relax(Cs, S0, N, S) :-
    foldl(relax_clause, Cs, S0, S1),
    (   S1 == S0 -> S = S0 ; N1 is N - 1, relax(Cs, S1, N1, S) ).
relax_clause(C, S0, S) :-
    clause_parts(C, H, Gs), pred_key(H, KH),
    foldl(need(S0), Gs, 0, Need),
    memberchk(KH-Old, S0),
    (   Need > Old -> selectchk(KH-Old, S0, KH-Need, S) ; S = S0 ).
need(S, \+ G, M0, M) :- !, pred_key(G, K), ( memberchk(K-V, S) -> M is max(M0, V + 1) ; M = M0 ).
need(S, G, M0, M) :- callable(G), \+ builtin(G), !, pred_key(G, K), ( memberchk(K-V, S) -> M is max(M0, V) ; M = M0 ).
need(_, _, M, M).

builtin(_ \= _). builtin(_ = _). builtin(neq(_, _)).
builtin(G) :- arith(G).
arith(_ is _). arith(between(_, _, _)). arith(_ =:= _). arith(_ < _). arith(_ > _). arith(_ >= _). arith(_ =< _). arith(_ =\= _).

least_model(Clauses, Input, Model) :-
    strata(Clauses, Strata),
    findall(V, member(_-V, Strata), Vs), max_list([0|Vs], Max),
    findall(F, (member(F, Input)), F0), sort(F0, DB0),
    numlist(0, Max, Levels),
    foldl(eval_stratum(Clauses, Strata), Levels, DB0, Model).

eval_stratum(Clauses, Strata, L, DB0, DB) :-
    include(in_stratum(Strata, L), Clauses, Cs),
    fix(Cs, DB0, DB).
in_stratum(Strata, L, C) :- clause_parts(C, H, _), pred_key(H, K), memberchk(K-L, Strata).

fix(Cs, DB0, DB) :-
    findall(H, ( member(C, Cs), copy_term(C, C1), clause_parts(C1, H, Gs),
                 order_goals(Gs, Gs1), prove_body(Gs1, DB0), ground(H) ), New0),
    sort(New0, New),
    ord_union(DB0, New, DB1),
    (   DB1 == DB0 -> DB = DB0 ; fix(Cs, DB1, DB) ).

order_goals(Gs, Ordered) :-                     % bind variables before tests
    partition(positive_goal, Gs, Pos, Rest), append(Pos, Rest, Ordered).
positive_goal(G) :- G \= (\+ _), \+ builtin(G).

prove_body([], _).
prove_body([\+ G|Gs], DB) :- !, \+ memberchk(G, DB), prove_body(Gs, DB).
prove_body([X \= Y|Gs], DB) :- !, X \== Y, prove_body(Gs, DB).
prove_body([neq(X, Y)|Gs], DB) :- !, X \== Y, prove_body(Gs, DB).
prove_body([X = Y|Gs], DB) :- !, X = Y, prove_body(Gs, DB).
% arithmetic: X is E needs E ground (X may be unbound); between/3 needs its bounds;
% a comparison needs both sides ground
prove_body([G|Gs], DB) :- arith(G), !, arith_ready(G), catch(G, E, arith_error(E)), prove_body(Gs, DB).
prove_body([G|Gs], DB) :- member(G, DB), prove_body(Gs, DB).

% ---------------------------------------------------------------- claim 2
program_reproduces(Program, Input, Observed, Result) :-
    least_model(Program, Input, M),
    check_observed(Observed, M, Result).

check_observed(Obs, M, Result) :-
    (   member(true(A), Obs), \+ memberchk(A, M) -> Result = refuted(missing(A))
    ;   member(false(A), Obs), memberchk(A, M) -> Result = refuted(unexpected(A))
    ;   length(Obs, N), Result = proved(all_observed_literals_hold(N))
    ).

% ---------------------------------------------------------------- claim 1
% Weights only: hidden unit H fires when the weighted sum of its active inputs exceeds
% its threshold; output atom A fires when the weighted sum of its firing hidden units
% exceeds its threshold. Input-predicate units (bias-only hidden units feeding atoms
% whose predicate has no other kind of unit) are removed and replaced by Input.
net_reproduces(NetFile, Input, Observed, Result) :-
    net_forward(NetFile, Input, Model),
    check_observed(Observed, Model, Result).

net_forward(NetFile, Input, Model) :-
    net_module(NetFile, NetM),
    findall(H-T, NetM:neuron(H, hidden, step, T), Hs),
    findall(A, NetM:neuron(out(A), output, _, _), Atoms),
    input_preds(NetM, Hs, Atoms, InPreds),
    findall(A, (member(A, Input), pred_key(A, K), memberchk(K, InPreds)), In0), sort(In0, In),
    unit_strata(NetM, Hs, Atoms, InPreds, Strata),
    findall(S, member(_-S, Strata), Ss), max_list([0|Ss], Max), numlist(0, Max, Levels),
    foldl(net_stratum(NetM, InPreds, Strata), Levels, In, Model).

user:file_search_path(library, '/home/claude/pl2ann/prolog').
net_module(File, M) :-
    setup_call_cleanup(open(File, read, S), read_term(S, (:- module(M, _)), []), close(S)),
    ( current_module(M) -> true ; load_files(File, [silent(true), imports([])]) ).

bias_unit(NetM, H) :- NetM:neuron(H, hidden, step, T), T < 0, \+ NetM:edge(_, H, _).

input_preds(NetM, _Hs, Atoms, InPreds) :-
    findall(K, ( member(A, Atoms), pred_key(A, K) ), Ks0), sort(Ks0, Ks),
    include(only_bias_fed(NetM, Atoms), Ks, InPreds).
only_bias_fed(NetM, Atoms, K) :-
    forall(( member(A, Atoms), pred_key(A, K), NetM:edge(H, out(A), _) ), bias_unit(NetM, H)).

unit_strata(NetM, _Hs, Atoms, InPreds, Strata) :-
    findall(A-0, member(A, Atoms), S0),
    length(Atoms, N), Lim is N + 2,
    relax_units(NetM, InPreds, S0, Lim, Strata).
relax_units(_, _, S, 0, S) :- !.
relax_units(NetM, InPreds, S0, N, S) :-
    findall(A-V, ( member(A-V0, S0),
                   findall(Need, ( NetM:edge(H, out(A), _), NetM:edge(in(B), H, W),
                                   memberchk(B-VB, S0), ( W < 0 -> Need is VB + 1 ; Need = VB ) ), Needs),
                   max_list([V0|Needs], V) ), S1),
    (   S1 == S0 -> S = S0 ; N1 is N - 1, relax_units(NetM, InPreds, S1, N1, S) ).

net_stratum(NetM, InPreds, Strata, L, On0, On) :-
    findall(A, ( member(A-L, Strata), pred_key(A, K), \+ memberchk(K, InPreds) ), Layer),
    net_fix(NetM, Layer, On0, On).
net_fix(NetM, Layer, On0, On) :-
    findall(A, ( member(A, Layer), \+ memberchk(A, On0), atom_fires(NetM, A, On0) ), New0),
    sort(New0, New), ord_union(On0, New, On1),
    (   On1 == On0 -> On = On0 ; net_fix(NetM, Layer, On1, On) ).

% input atoms are clamped (their bias units are replaced by Input), so atom_fires is
% only asked about non-input atoms, whose units are all genuine weighted units
atom_fires(NetM, A, On) :-
    NetM:neuron(out(A), output, _, TOut),
    findall(W, ( NetM:edge(H, out(A), W), hidden_fires(NetM, H, On) ), Ws),
    sum_list(Ws, S), S > TOut.
hidden_fires(NetM, H, On) :-
    NetM:neuron(H, hidden, step, T),
    findall(W, ( NetM:edge(in(B), H, W), memberchk(B, On) ), Ws),
    sum_list(Ws, S), S > T.

% ---------------------------------------------------------------- claim 3
equivalent(A, B, Targets, EdbSpec, Result) :-
    (   syntactic_derivation(A, B, Steps) -> Result = proved(syntactic(Steps))
    ;   exhaustive(A, B, Targets, EdbSpec, Result)
    ).

% B is reachable from A by removing duplicate literals, duplicate clauses and
% theta-subsumed clauses (each step preserves the least model for every input).
syntactic_derivation(A, B, Steps) :-
    normalise(A, NA), normalise(B, NB),
    simplify(NA, NB, [], Steps0), reverse(Steps0, Steps).
simplify(P, Goal, Acc, Acc) :- same_program(P, Goal), !.
simplify(P, Goal, Acc, Steps) :-
    step(P, P1, Why), !, simplify(P1, Goal, [Why|Acc], Steps).

step(P, P1, dup_literal(C)) :-
    select(C, P, Rest), C = (H :- Gs), dup_goal(Gs, Gs1), !, P1 = [(H :- Gs1)|Rest].
step(P, P1, dup_clause(C)) :-
    append(Pre, [C|Post], P), select(D, Post, Post1), clause_variant(C, D), !,
    append(Pre, [C|Post1], P1).
step(P, P1, subsumed(D, by(C))) :-
    select(D, P, Rest), member(C, Rest), subsumes_clause(C, D), !, P1 = Rest.

dup_goal(Gs, Gs1) :- append(Pre, [G|Post], Gs), member(G2, Post), G == G2, !, append(Pre, Post, Gs1).
subsumes_clause((H1 :- B1), (H2 :- B2)) :-          % C theta-subsumes D
    \+ \+ ( copy_term((H1 :- B1), (H :- B)), numbervars((H2 :- B2), 0, _),
            H = H2, subset_unify(B, B2) ).
subset_unify([], _).
subset_unify([G|Gs], B2) :- member(G, B2), subset_unify(Gs, B2).

normalise(P, N) :- maplist(norm_clause, P, N).
norm_clause((H :- B), (H :- Gs)) :- !, conj_list(B, Gs).
norm_clause(H, (H :- [])).
same_program(P, Q) :-
    length(P, N), length(Q, N),
    forall(member(C, P), (member(D, Q), clause_variant(C, D))),
    forall(member(D, Q), (member(C, P), clause_variant(C, D))).
clause_variant(C, D) :-                 % variant up to the order of body goals
    \+ \+ ( copy_term(C, (H :- B)), permutation(B, P), (H :- P) =@= D ).

% exhaustive check over every subset of the input atoms (small domains only)
exhaustive(A, B, Targets, edb(Preds, Consts), Result) :-
    findall(At, ( member(P/N, Preds), length(Args, N), maplist({Consts}/[X]>>member(X, Consts), Args),
                  At =.. [P|Args] ), Universe),
    length(Universe, U),
    (   U > 16 -> sampled(A, B, Targets, Universe, 2000, Result)
    ;   Total is 2 ** U,
        (   subset_of(Universe, Facts),
            least_model(A, Facts, MA), least_model(B, Facts, MB),
            target_atoms(MA, Targets, TA), target_atoms(MB, Targets, TB),
            TA \== TB
        ->  ord_subtract(TA, TB, OA), ord_subtract(TB, TA, OB),
            Result = refuted(input(Facts), only_in_a(OA), only_in_b(OB))
        ;   Result = proved(exhaustive(Total))
        )
    ).
subset_of([], []).
subset_of([X|Xs], [X|Ys]) :- subset_of(Xs, Ys).
subset_of([_|Xs], Ys) :- subset_of(Xs, Ys).
target_atoms(M, Targets, T) :- include({Targets}/[A]>>(pred_key(A, K), memberchk(K, Targets)), M, T0), sort(T0, T).

% ---------------------------------------------------------------- claim 4: Prolog <-> net
% Structural match. Each hidden unit is decoded from its weights alone into a ground clause:
%   head  = the output atom it feeds (weight > 0),
%   body  = in(B) with weight > 0  -> B,   weight < 0 -> \+ B,
%   check = threshold must equal (positive inputs - 0.5), i.e. the unit is an AND gate.
% The program is grounded over the network's constants; builtins (\=, =) are evaluated;
% instances that mention atoms without neurons are dropped. The two clause sets must match.
net_clauses(NetFile, Clauses) :-
    net_module(NetFile, NetM),
    findall(H-T, NetM:neuron(H, hidden, _Act, T), Hs),
    % the gain of a unit (1 in step/tanh mode, the derived weight W in sigmoid mode) is read
    % from its outgoing weight; every input weight must be +gain or -gain
    findall(C, ( member(H-T, Hs), NetM:edge(H, out(A), WO), WO > 0,
                 findall(B, (NetM:edge(in(B), H, W), abs(W - WO) < 1.0e-6), Pos),
                 findall(\+ B, (NetM:edge(in(B), H, W), abs(W + WO) < 1.0e-6), Neg),
                 length(Pos, NP), Expected is (NP - 0.5) * WO,
                 ( abs(T - Expected) < 1.0e-6 -> true
                 ; throw(not_an_and_unit(H, threshold(T), expected(Expected))) ),
                 append(Pos, Neg, Body0), msort(Body0, Body),
                 C = (A :- Body) ), Cs0),
    sort(Cs0, Clauses).

net_matches_program(NetFile, Program, Result) :-
    net_matches_program(NetFile, Program, [], Result).

% Domain = the facts of a pl2ann domain file (domain/2, range/3, type/3), or []. A variable
% at a typed argument position ranges over the intersection of its types' values, as pl2ann
% grounds it; any other variable ranges over every argument term in the net.
net_matches_program(NetFile, Program, Domain, Result) :-
    catch(net_clauses(NetFile, NetCs), E, (Result = refuted(E), !, fail)), !,
    net_module(NetFile, NetM),
    findall(A, NetM:neuron(out(A), output, _, _), Atoms),
    % the universe = every argument term of every atom and all of its subterms, so
    % compound and list arguments (pl2ann --term-depth) are grounded too
    findall(K, (member(A, Atoms), A =.. [_|As], member(T, As), sub_arg(T, K)), K0), sort(K0, Consts),
    findall(G, ( member(C, Program), copy_term(C, C1), clause_parts(C1, H, Gs),
                 term_variables(C1-Gs, Vs), typed_ranges(Domain, H, Gs, Consts, Vs, Ranges),
                 maplist([V-R]>>member(V, R), Ranges),
                 builtins_hold(Gs, Gs1), memberchk(H, Atoms),
                 forall(member(X, Gs1), (X = (\+ Y) -> memberchk(Y, Atoms) ; memberchk(X, Atoms))),
                 msort(Gs1, Body), G = (H :- Body) ), P0),
    sort(P0, ProgCs),
    ord_subtract(NetCs, ProgCs, OnlyNet), ord_subtract(ProgCs, NetCs, OnlyProg),
    length(NetCs, N),
    (   OnlyNet == [], OnlyProg == [] -> Result = proved(same_ground_clauses(N))
    ;   Result = refuted(only_in_net(OnlyNet), only_in_program(OnlyProg))
    ).
net_matches_program(_, _, _, _).

typed_ranges(Domain, H, Gs, Consts, Vs, Ranges) :-
    % no findall here: it would copy the literals and lose the link to Vs
    lits_of([H|Gs], Lits),
    maplist(var_range(Domain, Lits, Consts), Vs, Ranges).
var_range(Domain, Lits, Consts, V, V-R) :-
    findall(Vals, ( member(L, Lits), functor(L, P, A), between(1, A, I), arg(I, L, X), X == V,
                    memberchk(type(P/A, I, T), Domain), type_values(Domain, T, Vals) ), Sets),
    (   Sets = [] -> R = Consts
    ;   foldl([S, Acc0, Acc]>>intersection(Acc0, S, Acc), Sets, Consts, R0),
        Sets = [S0|_], intersection(S0, R0, R)
    ).
type_values(Domain, T, Vals) :-
    (   memberchk(domain(T, Vals), Domain) -> true
    ;   memberchk(range(T, Lo, Hi), Domain) -> numlist(Lo, Hi, Vals)
    ;   Vals = []
    ).

builtins_hold([], []).
builtins_hold([X \= Y|Gs], R) :- !, X \== Y, builtins_hold(Gs, R).
builtins_hold([neq(X, Y)|Gs], R) :- !, X \== Y, builtins_hold(Gs, R).
builtins_hold([X = Y|Gs], R) :- !, X == Y, builtins_hold(Gs, R).
builtins_hold([G|Gs], R) :- arith(G), !, ground(G), catch(G, E, arith_error(E)), builtins_hold(Gs, R).
builtins_hold([G|Gs], [G|R]) :- builtins_hold(Gs, R).

% Behavioural match for EVERY input over the net's input atoms (bounded proof).
net_equivalent_program(NetFile, Program, Targets, MaxInputs, Result) :-
    net_module(NetFile, NetM),
    findall(A, NetM:neuron(out(A), output, _, _), Atoms),
    findall(H-T, NetM:neuron(H, hidden, step, T), Hs),
    input_preds(NetM, Hs, Atoms, InPreds),
    include({InPreds}/[A]>>(pred_key(A, K), memberchk(K, InPreds)), Atoms, Universe),
    length(Universe, U),
    (   U > MaxInputs -> Result = unknown(too_many_inputs(U))
    ;   Total is 2 ** U,
        (   subset_of(Universe, Facts),
            net_forward(NetFile, Facts, MN), least_model(Program, Facts, MP),
            target_atoms(MN, Targets, TN), target_atoms(MP, Targets, TP), TN \== TP
        ->  ord_subtract(TN, TP, ON), ord_subtract(TP, TN, OP),
            Result = refuted(input(Facts), only_in_net(ON), only_in_program(OP))
        ;   Result = proved(all_inputs(Total))
        )
    ).

% more than 2^16 inputs: test a fixed pseudo-random sample (evidence, not a proof)
sampled(A, B, Targets, Universe, N, Result) :-
    set_random(seed(42)),
    (   between(1, N, _),
        include([_]>>(random(R), R < 0.3), Universe, Facts),
        least_model(A, Facts, MA), least_model(B, Facts, MB),
        target_atoms(MA, Targets, TA), target_atoms(MB, Targets, TB), TA \== TB
    ->  ord_subtract(TA, TB, OA), ord_subtract(TB, TA, OB),
        Result = refuted(input(Facts), only_in_a(OA), only_in_b(OB))
    ;   Result = passed_sample(N)
    ).

sub_arg(T, T).
sub_arg(T, S) :- compound(T), T =.. [_|As], member(A, As), sub_arg(A, S).

lits_of([], []).
lits_of([G|Gs], Ls) :- ( G = (\+ L) -> Ls = [L|R] ; callable(G) -> Ls = [G|R] ; Ls = R ), lits_of(Gs, R).

arith_ready(_ is E) :- !, ground(E).
arith_ready(between(L, H, _)) :- !, ground(L-H).
arith_ready(G) :- ground(G).

% an arithmetic error fails the goal; a time limit from an enclosing call is passed on
arith_error(E) :- ( E = time_limit_exceeded ; E = time_limit_exceeded(_) ), !, throw(E).
arith_error(_) :- fail.

:- encoding(utf8).
/*  induction_equivalence.pl -- the checker for mnns proof steps of rule induction_equivalence.

    A copy of S2A2's prolog/io_proof.pl (github.com/luciangreen/S2A2, commit 3936d3f), with only
    the module name changed, so that mnns's proof checker can re-prove the claim itself
    without loading S2A2. S2A2's io_proof.pl documentation follows.

    io_proof.pl -- prove a program found from input/output equal to a reference program, for
    every input of the declared types, not just the inputs that were tried.

    prove_equal(+Prog1, +Name1, +Prog2, +Name2, +ArgTypes, -Result)
        Prog1 and Prog2 are lists of clauses; Name1/N and Name2/N are the two predicates;
        ArgTypes gives a type for each argument (list(int), list(list(int)), int or any).
        Result is proved(Steps) or not_proved.

    The proof shows that the two predicates have the same answers on every input of the
    declared types (the same least model there). It is built from these steps, each of which
    keeps the answers the same:

      unfold      a call to a non-recursive predicate with one clause is replaced by that
                  clause's body (unfolding keeps the least model: Tamaki and Sato 1984);
      equation    a goal X = T in a clause body is solved, and the clause is instantiated;
      inline      V is E, where V is used only inside other arithmetic, is replaced by E in
                  those places (is/2 evaluates E either way);
      arithmetic  expressions are compared as polynomials with integer coefficients, so
                  2*X, X+X and X*2 are the same; other functions (//, mod, abs, max, min)
                  are compared argument by argument, with max and min commutative;
      tests       comparisons on integers are compared in a normal form: P =< 0, P =:= 0 or
                  P =\= 0, with P a polynomial whose coefficients have no common factor, so
                  X > 1, 1 < X and X >= 2 are the same test;
      integers    X == Y and X \== Y become X =:= Y and X =\= Y when both are integers, from
                  the declared types;
      residues    two tests that use E mod K only are compared on each residue 0..K-1
                  (E mod K takes no other values when K > 0);
      flip        (C -> A ; B) is the same as (not C -> B ; A) when C is a test;
      lemma       a call is replaced by a call of a predicate already proved equal to it, on
                  the types it is called with;
      invariant   a call P(L, M) made after max_list(L, M) (or min_list(L, M)) may assume that
                  every element of L is at most (at least) M; the pair P = Q is then proved
                  by induction for those inputs only: the tail of L keeps the invariant, and
                  in a step clause the head element X satisfies X =< M (X >= M). Tests are
                  then compared on the integers that satisfy it, by their thresholds;
      induction   a pair of predicates that both recurse on the tail of the same list
                  argument is proved by induction on that list: the induction hypothesis
                  replaces each recursive call on the tail.

    Two predicates are equal when their clauses can be paired off so that each pair, after
    the steps above, is the same clause up to renaming of variables and order of goals.
    The search for a pairing is a proof search: it either finds a proof or reports
    not_proved; it never reports proved for programs it has not matched.
*/
:- module(mnn_induction_equivalence, [prove_equal/6, show_proof/1]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).

% ================================================================ entry
prove_equal(P1, N1, P2, N2, Types, Result) :-
    length(Types, A),
    prepare(P1, Pr1, U1), prepare(P2, Pr2, U2),
    b_setval(io_proof_steps, []),
    Ctx = ctx(Pr1, Pr2, [], []),
    (   catch(call_with_inference_limit(once(prove_pair(N1/A, N2/A, Types, none, Ctx)), 20000000, R), _, fail),
        R \== inference_limit_exceeded
    ->  b_getval(io_proof_steps, S0), reverse(S0, S1), exclude([X]>>( X = proven(_, _, _, _) ), S1, S1a), dedup(S1a, S2),
        findall(unfold(K), ( member(K, U1) ; member(K, U2) ), Us),
        append(Us, S2, Steps), Result = proved(Steps)
    ;   Result = not_proved ).

step(S) :- b_getval(io_proof_steps, L), b_setval(io_proof_steps, [S|L]).

dedup([], []).
dedup([X|Xs], [X|Ys]) :- exclude(==(X), Xs, Xs1), dedup(Xs1, Ys).

show_proof(not_proved) :- format("    not proved~n").
show_proof(proved(Steps)) :-
    format("    proved for every input of the declared types:~n"),
    forall(member(S, Steps), ( step_text(S, T), format("      ~w~n", [T]) )).

step_text(unfold(K), T) :- format(atom(T), "unfold ~w (one clause, not recursive)", [K]).
step_text(pair(P, Q, induction(I), none), T) :- !, format(atom(T), "~w = ~w by induction on argument ~w", [P, Q, I]).
step_text(pair(P, Q, induction(I), Inv), T) :- !, inv_text(Inv, IT),
    format(atom(T), "~w = ~w by induction on argument ~w, for inputs where ~w", [P, Q, I, IT]).
step_text(pair(P, Q, direct, _), T) :- format(atom(T), "~w = ~w clause by clause", [P, Q]).
step_text(invariant(Inv, From), T) :- inv_text(Inv, IT),
    format(atom(T), "at the call, ~w (library fact about ~w), and the tail keeps it", [IT, From]).
step_text(rule(R), T) :- rule_text(R, T).
inv_text(upper(I, J), T) :- format(atom(T), "every element of argument ~w is at most argument ~w", [I, J]).
inv_text(lower(I, J), T) :- format(atom(T), "every element of argument ~w is at least argument ~w", [I, J]).
rule_text(arithmetic, 'arithmetic compared as polynomials').
rule_text(tests, 'tests compared in normal form').
rule_text(integers, '== and \\== on integers read as =:= and =\\=').
rule_text(residues, 'tests on E mod K compared on every residue').
rule_text(flip, 'if-then-else with the test negated and the branches swapped').
rule_text(inline, 'local is/2 values substituted into arithmetic').
rule_text(equation, 'body equations solved').
rule_text(assumption, 'tests compared on integers that satisfy the invariant').

% ================================================================ programs
% prepare(+Clauses, -prog(Clauses1, UserKeys, Recursive), -Unfolded): bodies as goal lists
% (if-then-else as ite(C, T, E)); single-clause non-recursive predicates unfolded
prepare(Cs0, prog(Cs, Keys, Rec), Unfolded) :-
    maplist(to_hb, Cs0, Cs1),
    findall(K, ( member(H-_, Cs1), key(H, K) ), K0), sort(K0, Keys),
    recursive_keys(Cs1, Keys, Rec),
    findall(K, ( member(K, Keys), \+ memberchk(K, Rec), findall(x, ( member(H-_, Cs1), key(H, K) ), [_]) ), Inl),
    maplist(unfold_clause(Cs1, Inl), Cs1, Cs2),
    maplist(normal_clause, Cs2, Cs),
    findall(K, ( member(K, Inl), used_in(K, Cs1) ), Unfolded).

used_in(K, Cs) :- member(_-B, Cs), sub_term(G, B), callable(G), \+ G = ite(_, _, _), key(G, K), !.

key(G, N/A) :- functor(G, N, A).

to_hb((H :- B), H-L) :- !, body_list(B, L).
to_hb(H, H-[]).

body_list(V, [call(V)]) :- var(V), !.
body_list((A, B), L) :- !, body_list(A, LA), body_list(B, LB), append(LA, LB, L).
body_list((C -> T ; E), [ite(CL, TL, EL)]) :- !, body_list(C, CL), body_list(T, TL), body_list(E, EL).
body_list(true, []) :- !.
body_list(\+ G, [N]) :- comparison(G), !, G =.. [Op, A, B], neg_op(Op, Op1), N =.. [Op1, A, B].
body_list(G, [G]).

comparison(G) :- compound(G), G =.. [Op, _, _], memberchk(Op, [<, >, =<, >=, =:=, =\=, ==, \==]).
neg_op(<, >=). neg_op(>, =<). neg_op(=<, >). neg_op(>=, <). neg_op(=:=, =\=). neg_op(=\=, =:=). neg_op(==, \==). neg_op(\==, ==).

% predicates on a cycle of the call graph
recursive_keys(Cs, Keys, Rec) :-
    findall(K-K2, ( member(H-B, Cs), key(H, K), sub_term(G, B), callable(G), G \= ite(_, _, _),
                    \+ is_list(G), key(G, K2), memberchk(K2, Keys) ), E0), sort(E0, Edges),
    include(self_reaching(Edges), Keys, Rec).
self_reaching(Edges, K) :- reaches(Edges, K, K, [K]).
reaches(Edges, From, To, _) :- memberchk(From-To, Edges), !.
reaches(Edges, From, To, Seen) :- member(From-M, Edges), \+ memberchk(M, Seen), reaches(Edges, M, To, [M|Seen]), !.

unfold_clause(Cs, Inl, H-B, H-B1) :- unfold_goals(B, Cs, Inl, 6, B1).
unfold_goals([], _, _, _, []).
unfold_goals([G|Gs], Cs, Inl, D, Out) :-
    unfold_goal(G, Cs, Inl, D, G1), unfold_goals(Gs, Cs, Inl, D, Gs1), append(G1, Gs1, Out).
unfold_goal(ite(C, T, E), Cs, Inl, D, [ite(C1, T1, E1)]) :- !,
    unfold_goals(C, Cs, Inl, D, C1), unfold_goals(T, Cs, Inl, D, T1), unfold_goals(E, Cs, Inl, D, E1).
unfold_goal(G, Cs, Inl, D, Out) :-
    D > 0, callable(G), key(G, K), memberchk(K, Inl), !,
    member(H-B, Cs), key(H, K), !, copy_term(H-B, H1-B1),
    (   G = H1 -> D1 is D - 1, unfold_goals(B1, Cs, Inl, D1, Out) ; Out = [fail] ).
unfold_goal(G, _, _, _, [G]).

% solve body equations at the top of a body (instantiating the clause) and substitute
% local is/2 values that are used only inside arithmetic
normal_clause(H-B, H-B2) :- solve_equations(B, B1), inline_is(H, B1, B2).
solve_equations([], []).
solve_equations([X = Y|Gs], Out) :- !, ( X = Y -> solve_equations(Gs, Out) ; Out = [fail] ).
solve_equations([G|Gs], [G|Out]) :- solve_equations(Gs, Out).

inline_is(H, B, Out) :-
    (   select(V is E, B, Rest), var(V), \+ occurs_in(V, H), arith_only(V, Rest)
    ->  subst_arith(Rest, V, E, Rest1), inline_is(H, Rest1, Out)
    ;   Out = B ).
occurs_in(V, T) :- term_variables(T, Vs), member(W, Vs), W == V, !.
arith_only(V, Gs) :- occurs_in(V, Gs), forall(( member(G, Gs), occurs_in(V, G) ), arith_goal_use(V, G)).
arith_goal_use(V, _ is E) :- !, occurs_in(V, E).
arith_goal_use(_, G) :- comparison(G), \+ G = (_ == _), \+ G = (_ \== _), !.
arith_goal_use(V, ite(C, T, E)) :- forall(( member(G, C) ; member(G, T) ; member(G, E) ), ( occurs_in(V, G) -> arith_goal_use(V, G) ; true )).
subst_arith(T, V, E, E) :- T == V, !.
subst_arith(T, _, _, T) :- ( var(T) ; atomic(T) ), !.
subst_arith(T, V, E, T1) :- T =.. [F|As], subst_args(As, V, E, As1), T1 =.. [F|As1].
subst_args([], _, _, []).
subst_args([A|As], V, E, [B|Bs]) :- subst_arith(A, V, E, B), subst_args(As, V, E, Bs).

clauses_of(prog(Cs, _, _), K, Ks) :- findall(H-B, ( member(H-B, Cs), key(H, K) ), Ks).
user_key(prog(_, Keys, _), K) :- memberchk(K, Keys).
is_rec(prog(_, _, Rec), K) :- memberchk(K, Rec).

% structural recursion on argument I: each head has [] or [_|T] there, and each recursive
% call takes the tail T at I
structural(Prog, K, I) :-
    clauses_of(Prog, K, Cs), Cs = [H0-_|_], functor(H0, _, A), between(1, A, I),
    forall(member(H-B, Cs),
           ( arg(I, H, X), nonvar(X), ( X == [] ; X = [_|T], var(T) ),
             forall(( sub_term(G, B), callable(G), \+ G = ite(_, _, _), \+ is_list(G), key(G, K) ),
                    ( X = [_|T1], arg(I, G, Y), Y == T1 )) )), !.

% ================================================================ pairs of predicates
% prove_pair(+K1, +K2, +Types, +Invariant, +Ctx): Invariant is none, upper(I, J) (every element
% of the list at argument I is at most argument J) or lower(I, J); the pair is proved for the
% inputs where it holds
prove_pair(K1, K2, Types, Inv, Ctx) :-
    b_getval(io_proof_steps, S0),
    (   member(proven(K1, K2, Ts0, Inv0), S0), Ts0 =@= Types, Inv0 == Inv -> true   % same types and invariant
    ;   Ctx = ctx(P1, P2, Cur, _),
        clauses_of(P1, K1, C1s), clauses_of(P2, K2, C2s),
        length(C1s, N), length(C2s, N), N > 0,
        (   ( is_rec(P1, K1) ; is_rec(P2, K2) )
        ->  structural(P1, K1, I), structural(P2, K2, I), nth1(I, Types, TI), ( TI = list(_) ; TI == any ),
            ( Inv = none -> true ; arg(1, Inv, I) ),
            How = induction(I), Cur1 = [K1-K2-I-Inv|Cur]
        ;   Inv == none, How = direct, Cur1 = Cur ),
        match_sets(C1s, C2s, Types, Inv, ctx(P1, P2, Cur1, [])),
        copy_term(Types, Ts1), step(proven(K1, K2, Ts1, Inv)), step(pair(K1, K2, How, Inv))
    ).

match_sets([], [], _, _, _).
match_sets([C|Cs], Ds, Types, Inv, Ctx) :- select(D, Ds, Rest), match_clause(C, D, Types, Inv, Ctx), match_sets(Cs, Rest, Types, Inv, Ctx).

match_clause(C1, C2, Types, Inv, ctx(P1, P2, Cur, _)) :-
    copy_term(C1, H1-B1), copy_term(C2, H2-B2),
    term_variables(H1-B1, V1), term_variables(H2-B2, V2), length(V1, N1), length(V2, N2),
    H1 =.. [_|A1], H2 =.. [_|A2], A1 =@= A2, A1 = A2,
    types_env(A1, Types, Env0), infer(B1, Env0, Env1), infer(B2, Env1, Env),
    assumptions(Inv, H1, Env, As),
    match_goals(B1, B2, Env, ctx(P1, P2, Cur, B1), H1, [], Def),
    deferred_all(Def, Env-As),
    distinct_vars(V1, N1), distinct_vars(V2, N2).

% the invariant gives a fact about the head element: X =< M for upper, X >= M for lower
assumptions(none, _, _, []) :- !.
assumptions(Inv, H, Env, [C]) :-
    Inv =.. [K, I, J], arg(I, H, L), nonvar(L), L = [X|_], !, arg(J, H, M),
    ( K == upper -> canon(X =< M, Env, C, _) ; canon(X >= M, Env, C, _) ).
assumptions(_, _, _, []).

deferred_all([], _).
deferred_all([D|Ds], EA) :- deferred(D, EA), deferred_all(Ds, EA).

distinct_vars(Vs, N) :- maplist(var, Vs), term_variables(Vs, Ws), length(Ws, N).

% match_goals(+B1, +B2, +Env, +Ctx, +Head1, +Def0, -Def): every goal of B1 against a distinct
% goal of B2, in any order; arithmetic and tests are checked after all bindings are made
match_goals([], [], _, _, _, D, D).
match_goals([G|Gs], B2, Env, Ctx, H, D0, D) :-
    select(G2, B2, Rest), match_goal(G, G2, Env, Ctx, H, D0, D1),
    match_goals(Gs, Rest, Env, Ctx, H, D1, D).

match_goal(ite(C1, T1, E1), ite(C2, T2, E2), Env, Ctx, H, D0, D) :- !,
    (   C1 = [T], C2 = [U], test_goal(T), test_goal(U)
    ->  (   match_goals(T1, T2, Env, Ctx, H, [test(T, U)|D0], D1), match_goals(E1, E2, Env, Ctx, H, D1, D)
        ;   match_goals(T1, E2, Env, Ctx, H, [test(T, not(U)), rule(flip)|D0], D1), match_goals(E1, T2, Env, Ctx, H, D1, D) )
    ;   match_goals(C1, C2, Env, Ctx, H, D0, D1), match_goals(T1, T2, Env, Ctx, H, D1, D2), match_goals(E1, E2, Env, Ctx, H, D2, D) ).
match_goal(V1 is E1, V2 is E2, _, _, _, D, [arith(E1, E2)|D]) :- !, V1 = V2.
match_goal(T, U, _, _, _, D, [test(T, U)|D]) :- test_goal(T), test_goal(U), !.
match_goal(X1 = Y1, G2, _, _, _, D, D) :- !, ( G2 = (X1 = Y1) ; G2 = (Y1 = X1) ).
match_goal(G1, G2, Env, Ctx, H, D, D) :-
    Ctx = ctx(P1, P2, Cur, Body), callable(G1), callable(G2), key(G1, K1), key(G2, K2),
    (   user_key(P1, K1)
    ->  user_key(P2, K2),
        G1 =.. [_|As1], G2 =.. [_|As2], As1 = As2,
        (   memberchk(K1-K2-I-Inv, Cur)
        ->  arg(I, H, X), nonvar(X), X = [_|T], nth1(I, As1, Y), Y == T,
            ( Inv = none -> true ; arg(2, Inv, J), arg(J, H, MH), nth1(J, As1, MC), MC == MH )
        ;   maplist(arg_type(Env), As1, Ts),
            (   prove_pair(K1, K2, Ts, none, Ctx) -> true
            ;   call_invariant(Body, As1, Inv, From), step(invariant(Inv, From)), prove_pair(K1, K2, Ts, Inv, Ctx) ) )
    ;   \+ user_key(P2, K2), K1 == K2, G1 = G2 ).

% call_invariant(+Body, +CallArgs, -Invariant, -From): library facts in the calling clause.
% max_list(L, M) means every element of L is at most M; min_list(L, M), at least M. A call
% with L at argument I and M at argument J gets upper(I, J) or lower(I, J).
call_invariant(Body, As, Inv, From) :-
    member(G, Body), G =.. [F, L, M], memberchk(F-K, [max_list-upper, min_list-lower]),
    nth1(I, As, L1), L1 == L, nth1(J, As, M1), M1 == M, I \== J,
    Inv =.. [K, I, J], format(atom(From), "~w/2", [F]).

test_goal(G) :- comparison(G).

deferred(rule(R), _) :- !, step(rule(R)).
deferred(arith(E1, E2), _) :- !, poly(E1, P1), poly(E2, P2), ( P1 == P2 -> true ; fail ), ( E1 =@= E2 -> true ; step(rule(arithmetic)) ).
deferred(test(T, U), Env-As) :- canon(T, Env, C1, I1), canon_maybe_neg(U, Env, C2, I2),
    (   C1 == C2 -> true
    ;   residue_equal(C1, C2) -> step(rule(residues))
    ;   As = [A|_], assume_equal(C1, C2, A), step(rule(assumption)) ),
    ( T =@= U -> true ; step(rule(tests)) ),
    ( ( I1 == yes ; I2 == yes ) -> step(rule(integers)) ; true ).
canon_maybe_neg(not(U), Env, C, I) :- !, canon(U, Env, C0, I), neg_canon(C0, C).
canon_maybe_neg(U, Env, C, I) :- canon(U, Env, C, I).

% ================================================================ types
types_env(As, Ts, Env) :- foldl(type_pat, As, Ts, [], Env).
type_pat(A, T, E0, E) :- var(A), !, ( var(T) -> E = E0 ; E = [A-T|E0] ).
type_pat([H|Tl], T, E0, E) :- nonvar(T), T = list(ET), !, type_pat(H, ET, E0, E1), type_pat(Tl, T, E1, E).
type_pat(_, _, E, E).

arg_type(Env, A, T) :- ( var(A) -> ( lookup(A, Env, T0) -> T = T0 ; T = any ) ; integer(A) -> T = int ; A = [H|_], arg_type(Env, H, ET), ET \== any -> T = list(ET) ; T = any ).
lookup(V, Env, T) :- member(W-T, Env), W == V, !.
int(V, Env) :- integer(V) -> true ; var(V), lookup(V, Env, T), T == int.

infer(Gs, E0, E) :- foldl(infer_goal, Gs, E0, E1), foldl(infer_goal, Gs, E1, E).
infer_goal(ite(C, T, F), E0, E) :- !, append([C, T, F], Gs), foldl(infer_goal, Gs, E0, E).
infer_goal(V is _, E0, E) :- var(V), !, add(V, int, E0, E).
infer_goal(G, E0, E) :- G =.. [F, L, V], memberchk(F, [min_list, max_list, sum_list]), !, ( arg_type(E0, L, list(int)) -> add(V, int, E0, E) ; E = E0 ).
infer_goal(length(_, V), E0, E) :- !, add(V, int, E0, E).
infer_goal(G, E0, E) :- G =.. [F, L, R], memberchk(F, [msort, sort, reverse]), !, ( arg_type(E0, L, T), T \== any -> type_pat(R, T, E0, E) ; E = E0 ).
infer_goal(last(L, V), E0, E) :- !, ( arg_type(E0, L, list(T)) -> type_pat(V, T, E0, E) ; E = E0 ).
infer_goal(L = R, E0, E) :- !, ( arg_type(E0, L, T), T \== any -> type_pat(R, T, E0, E) ; arg_type(E0, R, T), T \== any -> type_pat(L, T, E0, E) ; E = E0 ).
infer_goal(append(A, _, C), E0, E) :- !, ( arg_type(E0, A, T), T \== any -> type_pat(C, T, E0, E) ; E = E0 ).
infer_goal(_, E, E).
add(V, T, E0, E) :- ( var(V), \+ lookup(V, E0, _) -> E = [V-T|E0] ; E = E0 ).

% ================================================================ polynomials
% poly(+Expr, -P): P is a sorted list Monomial-Coefficient, a monomial a sorted list of atoms
% (variables or uninterpreted terms); zero coefficients dropped
poly(V, [[V]-1]) :- var(V), !.
poly(N, P) :- integer(N), !, ( N =:= 0 -> P = [] ; P = [[]-N] ).
poly(A + B, P) :- !, poly(A, PA), poly(B, PB), padd(PA, PB, P).
poly(A - B, P) :- !, poly(A, PA), poly(B, PB), pneg(PB, NB), padd(PA, NB, P).
poly(-A, P) :- !, poly(A, PA), pneg(PA, P).
poly(A * B, P) :- !, poly(A, PA), poly(B, PB), pmul(PA, PB, P).
poly(E, [[At]-1]) :- compound(E), !, E =.. [F|As], maplist([A, p(Q)]>>poly(A, Q), As, Ns),
    ( memberchk(F, [max, min]) -> msort(Ns, Ns1) ; Ns1 = Ns ), At =.. [F|Ns1].
poly(E, [[E]-1]).

padd(A, B, P) :- append(A, B, C), keysort(C, S), combine(S, P).
combine([], []).
combine([M-C|R], P) :- take_same(M, R, C, T, R1), ( T =:= 0 -> P = P1 ; P = [M-T|P1] ), combine(R1, P1).
take_same(M, [M2-C2|R], C0, C, R1) :- M2 == M, !, C1 is C0 + C2, take_same(M, R, C1, C, R1).
take_same(_, R, C, C, R).
pneg(P, N) :- maplist([M-C, M-D]>>( D is -C ), P, N).
% (no findall here: it would copy the variables in the monomials)
pmul(A, B, P) :- foldl(pmul_term(B), A, [], Ps), padd(Ps, [], P).
pmul_term(B, M1-C1, Acc, Acc1) :- foldl(pmul_one(M1, C1), B, Acc, Acc1).
pmul_one(M1, C1, M2-C2, Acc, [M-C|Acc]) :- append(M1, M2, M0), msort(M0, M), C is C1 * C2.

% ================================================================ tests in normal form
% canon(+Test, +Env, -Normal, -UsedIntegers): le(P) for P =< 0, eq(P), ne(P), or truth(B)
canon(A == B, Env, C, yes) :- int(A, Env), int(B, Env), !, canon(A =:= B, Env, C, _).
canon(A \== B, Env, C, yes) :- int(A, Env), int(B, Env), !, canon(A =\= B, Env, C, _).
canon(G, _, C, no) :- G =.. [Op, A, B], memberchk(Op, [<, >, =<, >=, =:=, =\=]), !,
    poly(A - B, P),
    (   Op == (<)   -> padd(P, [[]-1], Q), norm_le(Q, C)
    ;   Op == (=<)  -> norm_le(P, C)
    ;   Op == (>)   -> pneg(P, N), padd(N, [[]-1], Q), norm_le(Q, C)
    ;   Op == (>=)  -> pneg(P, N), norm_le(N, C)
    ;   Op == (=:=) -> norm_eq(eq, P, C)
    ;   norm_eq(ne, P, C) ).
canon(G, _, opaque(G), no).

split_const(P, C, Q) :- ( select([]-C0, P, Q) -> C = C0 ; C = 0, Q = P ).
coeff_gcd(Q, G) :- foldl([_-C, G0, G1]>>( G1 is gcd(G0, abs(C)) ), Q, 0, G).

norm_le(P, C) :-
    split_const(P, K, Q),
    (   Q == [] -> ( K =< 0 -> C = truth(true) ; C = truth(false) )
    ;   coeff_gcd(Q, G), K1 is -div(-K, G),
        pdiv(Q, G, Q1),
        ( K1 =:= 0 -> P1 = Q1 ; padd(Q1, [[]-K1], P1) ), C = le(P1) ).
norm_eq(Kind, P, C) :-
    split_const(P, K, Q),
    (   Q == [] -> ( ( K =:= 0 ) == ( Kind == eq ) -> C = truth(true) ; C = truth(false) )
    ;   coeff_gcd(Q, G),
        (   K mod G =\= 0 -> ( Kind == eq -> C = truth(false) ; C = truth(true) )
        ;   pdiv(P, G, P1),
            P1 = [_-Lead|_], ( Lead < 0 -> pneg(P1, P2) ; P2 = P1 ), C =.. [Kind, P2] ) ).

pdiv([], _, []).
pdiv([M-X|P], G, [M-Y|Q]) :- Y is X // G, pdiv(P, G, Q).

neg_canon(le(P), C) :- pneg(P, N), padd(N, [[]-1], Q), norm_le(Q, C).
neg_canon(eq(P), ne(P)).
neg_canon(ne(P), eq(P)).
neg_canon(truth(true), truth(false)).
neg_canon(truth(false), truth(true)).
neg_canon(opaque(G), opaque(\+ G)).

% residue_equal(+C1, +C2): both tests use only atoms E mod K (K from 2 to 6); they agree on
% every assignment of residues 0..K-1 to those atoms
residue_equal(C1, C2) :-
    mod_atoms(C1-C2, Ats), Ats \== [],
    forall(residue_assignment(Ats, As), ( eval_canon(C1, As, B), eval_canon(C2, As, B) )).
mod_atoms(T, Ats) :-
    collect_mods(T, [], A0), reverse(A0, Ats), Ats = [_|_],
    T = C1-C2, forall(( member(C, [C1, C2]), C =.. [_, P], is_list(P), member(M-_, P), member(X, M) ), ( nonvar(X), memberchk_eq(X, Ats) )).
memberchk_eq(X, L) :- member(Y, L), Y == X, !.
% the atoms E mod K in a term, without copying their variables
collect_mods(T, A0, A) :- var(T), !, A = A0.
collect_mods(T, A0, A) :- atomic(T), !, A = A0.
collect_mods(T, A0, A) :-
    (   T = mod(p(_), p([[]-K])), integer(K), K >= 2, K =< 6, \+ memberchk_eq(T, A0) -> A1 = [T|A0] ; A1 = A0 ),
    T =.. [_|As], foldl(collect_mods, As, A1, A).
residue_assignment([], []).
residue_assignment([A|As], [A-R|Rs]) :- A = mod(_, p([[]-K])), K1 is K - 1, between(0, K1, R), residue_assignment(As, Rs).
eval_canon(truth(B), _, B) :- !.
eval_canon(C, As, B) :- C =.. [Kind, P], eval_poly(P, As, V),
    (   Kind == le -> ( V =< 0 -> B = true ; B = false )
    ;   Kind == eq -> ( V =:= 0 -> B = true ; B = false )
    ;   ( V =\= 0 -> B = true ; B = false ) ).
eval_poly([], _, 0).
eval_poly([M-C|P], As, V) :- eval_mono(M, As, MV), eval_poly(P, As, V0), V is V0 + C * MV.
eval_mono([], _, 1).
eval_mono([X|Xs], As, V) :- member(Y-R, As), Y == X, !, eval_mono(Xs, As, V0), V is R * V0.

% assume_equal(+C1, +C2, +A): on the integers where the assumption A holds, the tests C1 and C2
% agree. All three must be tests on one value v = Q (or -Q), each a threshold set: P =< 0,
% P =:= 0 or P =\= 0 with P = +-Q + c. Such sets change only at their thresholds, so they are
% compared on every integer from below the smallest threshold to above the largest.
assume_equal(C1, C2, A) :-
    A = le(PA), split_const(PA, _, Q), Q \== [],
    maplist(one_d(Q), [C1, C2, A], Fs),
    findall(T, ( member(f(_, S, C), Fs), T is -S * C ), Ts0), msort(Ts0, Ts),
    Ts = [Lo|_], last(Ts, Hi), L is Lo - 2, U is Hi + 2,
    Fs = [F1, F2, FA],
    forall(( between(L, U, V), holds(FA, V) ), ( holds(F1, V) -> holds(F2, V) ; \+ holds(F2, V) )).
one_d(Q, C, f(Kind, S, K)) :-
    C =.. [Kind, P], memberchk(Kind, [le, eq, ne]), split_const(P, K, QP),
    (   QP == Q -> S = 1 ; pneg(Q, NQ), QP == NQ -> S = -1 ).
holds(f(le, S, K), V) :- S * V + K =< 0.
holds(f(eq, S, K), V) :- S * V + K =:= 0.
holds(f(ne, S, K), V) :- S * V + K =\= 0.

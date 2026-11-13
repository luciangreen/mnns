:- encoding(utf8).
/*  s2a2_fold.pl -- the checker for mnns proof steps of rule fold_derivation.

    A copy of S2A2's prolog/fold.pl (github.com/luciangreen/S2A2, commit cf72bda), with only the
    module name changed (fold -> mnn_fold), so that mnns's proof checker can repeat a
    derivation and its verification without loading S2A2. S2A2's documentation follows.

    fold.pl -- spec to algorithm: derive an efficient program from a naive one by
    unfold/fold transformation (Burstall and Darlington 1977; Tamaki and Sato 1984),
    with eureka definitions, a database of proved lemmas, lemma discovery and a learned
    choice of strategy.

    S2A2's other operators only make a program smaller. Deriving a new algorithm
    sometimes needs the opposite first: introduce a new predicate (a "eureka"
    definition), unfold it, rewrite with a lemma, then FOLD the result back into a
    call to the new predicate.

    PROGRAMS are lists of clauses Head-BodyList. Bodies may use is/2 and comparisons.
    TYPES are declared by their constructors (set_types/1); the defaults are
        list(E): [] | [E|list(E)]      tree(E): leaf | node(tree(E),E,tree(E))
        nat:     0  | s(nat)
    with the base types int, num and any.

    RULES (each with the side condition that makes it sound)
      define     add  d(V1..Vn) :- G1,...,Gk  for a new name d
      unfold     replace a clause by all its resolvents on one user literal
      fold       replace an instance of a definition's body by its head; the definition's
                 local variables must map to distinct variables used nowhere else in the
                 clause (Tamaki-Sato), and a clause from a definition was unfolded first
      lemma      replace an instance of one side of a lemma in the database by the other,
                 under the same local-variable condition
      merge      unify two calls of one predicate with identical first arguments
                 (an instance of a clause; equality then rests on functionality)
      normalise  unfold a literal whose case argument is a constructor and that matches at
                 most one clause; evaluate is/2 and comparisons on ground arguments

    STRATEGIES (tried in a learned order, see learn_strategies/2)
      deforest   a conjunctive definition p :- q, r is unfolded on its induction variable
                 and folded back: the intermediate structure disappears
      accumulate a recursive call whose result is consumed afterwards gets a definition that
                 generalises the consumer's other arguments into an accumulator
      tuple      two recursive calls on related arguments (N and s(N)) get a definition that
                 computes both results together
      fuse       the recursive call and the one literal that consumes its result get one
                 definition, unfolded on the consumer's case argument (flatten without append)
    Each searches by iterative deepening for unfold/lemma/merge/fold steps until every
    step clause of the new predicate calls only new predicates and builtins.

    DATABASE: a lemma about user predicates is admitted only after prove_lemma/3 proves it
    (both sides deforested to the same program). Arithmetic facts (associativity of +, * and max)
    are axioms of the integers.
    DISCOVERY: when a strategy gets stuck, discover_lemmas/4 conjectures lemmas from the
    stuck clauses (associativity and commutativity of a predicate that chains with itself,
    associativity of an arithmetic operator), proves or refutes each, and the strategy is
    retried with the proved ones.

    CORRECTNESS of a derived program R against its specification S, for a target predicate
    in a mode whose inputs have declared types (verify/5):
      * deforest without lemmas or merges: unfold/fold preserves the least model exactly
        (Tamaki-Sato), so R and S agree in every mode.
      * otherwise every step keeps every clause true in the least model of S plus the
        definitions, so each answer of R is an answer of S (soundness); then
          total(R, p, Mode)        R answers every input of the declared types
          functional(S, p, Mode)   S has at most one answer per input
        give the same answers on every input of those types; and if also
          slot_type(S, p, I, T)    every answer of S has the declared type at each input
        the least models are equal, so R and S agree in every mode (correct answers; which
        queries terminate may still differ). Integer axioms are sound where their variables
        are integers; verify/5 reports whether every is/2 in R is on integers.
      * bounded_equal/7 compares two programs on every input up to a size.
*/
:- module(mnn_fold, [ set_types/1, default_types/1, clauses/2, show/1,
                  unfold/4, fold_with/3, lemma_step/4, merge_step/3,
                  spec_to_algorithm/5, spec_to_algorithm/6, strategies/1,
                  prove_lemma/3, discover_lemmas/4, axiom/4,
                  total/3, total/4, functional/3, slot_type/4, verify/5,
                  bounded_equal/7, answers/3, steps/4, cost/4, same_clauses/2,
                  features/3, learn_strategies/2, choose_order/3 ]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).

% ---------------------------------------------------------------- types
:- dynamic type_decl/2.
default_types([ type(list(E), [[], [E|list(E)]]),
                type(tree(E), [leaf, node(tree(E), E, tree(E))]),
                type(nat, [0, s(nat)]) ]).
set_types(Ds) :- retractall(type_decl(_, _)), forall(member(type(T, Cs), Ds), assertz(type_decl(T, Cs))).
:- initialization(( default_types(D), set_types(D) )).

% constructor(+Type, ?Name/Arity, -ArgTypes)
constructor(T, F/A, ATs) :-
    nonvar(T), type_decl(T0, Cs0), copy_term(T0-Cs0, T1-Cs), T1 = T,
    member(C, Cs), functor(C, F, A), C =.. [_|ATs].
% any declared type with this constructor (for inference)
constructor_any(T, F/A, ATs) :-
    type_decl(T0, Cs0), copy_term(T0-Cs0, T-Cs), member(C, Cs), functor(C, F, A), C =.. [_|ATs].

base_type(T) :- memberchk(T, [any, int, num]).

% type_le(S, T): every value of type S is a value of type T
type_le(_, T) :- T == any, !.
type_le(S, T) :- S == T, !.
type_le(S, T) :- S == int, T == num, !.
type_le(S, T) :- nonvar(S), nonvar(T), \+ base_type(S), \+ base_type(T),
    S =.. [F|As], T =.. [F|Bs], maplist(type_le, As, Bs).

% ---------------------------------------------------------------- representation
clauses([], []).
clauses([C|Cs], [H-B|Rs]) :- ( C = (H :- Bd) -> conj(Bd, B) ; H = C, B = [] ), clauses(Cs, Rs).
conj((A, B), L) :- !, conj(A, LA), conj(B, LB), append(LA, LB, L).
conj(true, []) :- !.
conj(G, [G]).

key(G, N/A) :- functor(G, N, A).
clauses_of(P, K, Cs) :- findall(H-B, ( member(H-B, P), key(H, K) ), Cs).

builtin(G) :- compound(G), functor(G, F, 2), memberchk(F, [is, <, >, =<, >=, =:=, =\=, =]), !.
user_lit(G) :- \+ builtin(G).
comparison(G) :- compound(G), functor(G, F, 2), memberchk(F, [<, >, =<, >=, =:=, =\=]).

show(Cs) :- forall(member(C, Cs), show_clause(C)).
show_clause(H-B) :-
    copy_term(H-B, H1-B1), numbervars(H1-B1, 0, _),
    (   B1 == [] -> format("    ~p.~n", [H1])
    ;   lits_atom(B1, S), format("    ~p :- ~w.~n", [H1, S]) ).
lits_atom(Gs, S) :- maplist([G, A]>>format(atom(A), "~p", [G]), Gs, As), atomic_list_concat(As, ', ', S).

vmember(V, L) :- member(X, L), X == V, !.
vsub(Xs, Ys, Zs) :- exclude({Ys}/[X]>>vmember(X, Ys), Xs, Zs).
vint(Xs, Ys, Zs) :- include({Ys}/[X]>>vmember(X, Ys), Xs, Zs).
pairs_of([], [], []).
pairs_of([A|As], [B|Bs], [A-B|R]) :- pairs_of(As, Bs, R).

% the argument a predicate's clauses analyse by cases (a constructor in every head)
case_pos(P, K, I) :-
    clauses_of(P, K, Cs), Cs = [H0-_|_], functor(H0, _, A), between(1, A, I),
    forall(member(H-_, Cs), ( arg(I, H, X), nonvar(X) )), !.

% ---------------------------------------------------------------- unfold and normalise
unfold(Spec, H-B, J, Cs) :-
    nth1(J, B, L), user_lit(L), key(L, K), clauses_of(Spec, K, Ds), Ds \== [],
    findall(H1-B1, ( copy_term(H-B, H1-B0), nth1(J, B0, L1, Rest),
                     member(D, Ds), copy_term(D, DH-DB),
                     unify_with_occurs_check(L1, DH),
                     J0 is J - 1, length(Pre, J0), append(Pre, Post, Rest),
                     append([Pre, DB, Post], B1) ), Cs).

normalise(Spec, DefKs, C0, Out) :- copy_term(C0, C), normalise_(Spec, DefKs, C, Out).
normalise_(Spec, DefKs, C, Out) :-
    C = H-B,
    (   nth1(J, B, L), builtin(L), ground_builtin(L)
    ->  nth1(J, B, _, B1),
        ( catch(eval_builtin(L), _, fail) -> normalise_(Spec, DefKs, H-B1, Out) ; Out = failed )
    ;   nth1(J, B, L), user_lit(L), key(L, K), \+ memberchk(K, DefKs), case_pos(Spec, K, I),
        arg(I, L, X), nonvar(X), unfold(Spec, C, J, Cs), length(Cs, N), N =< 1
    ->  ( Cs = [C1] -> normalise_(Spec, DefKs, C1, Out) ; Out = failed )
    ;   Out = C
    ).
ground_builtin(X is E) :- !, ground(E), ( var(X) ; number(X) ).
ground_builtin(L) :- comparison(L), ground(L).
eval_builtin(X is E) :- !, V is E, X = V.
eval_builtin(L) :- call(L).

% ---------------------------------------------------------------- matching
match_goals([], _, []).
match_goals([P|Ps], B, [I|Is]) :-
    nth1(I, B, G), subsumes_term(P, G), P = G, match_goals(Ps, B, Is), \+ memberchk(I, Is).

others(B, Idx, Os) :- others_(B, 1, Idx, Os).
others_([], _, _, []).
others_([G|Gs], I, Idx, Os) :- I1 is I + 1,
    ( memberchk(I, Idx) -> Os = Os1 ; Os = [G|Os1] ), others_(Gs, I1, Idx, Os1).

replace_at(B, Idx, New, B1) :- min_list(Idx, M), rep(B, 1, Idx, M, New, B1).
rep([], _, _, _, _, []).
rep([G|Gs], I, Idx, M, New, Out) :- I1 is I + 1,
    (   I == M -> append(New, Rest, Out)
    ;   memberchk(I, Idx) -> Out = Rest
    ;   Out = [G|Rest] ),
    rep(Gs, I1, Idx, M, New, Rest).

% local variables are distinct variables that occur nowhere else in the clause
locals_ok(Ex, H, B, Idx, Extra) :-
    maplist(var, Ex), sort(Ex, S), length(S, N), length(Ex, N),
    others(B, Idx, Os), term_variables(H-Os-Extra, OV),
    \+ ( member(E, Ex), vmember(E, OV) ).

% ---------------------------------------------------------------- steps
fold_with(def(DH0, DB0), H-B, H-B1) :-
    copy_term(DH0-DB0, DH-DB),
    term_variables(DH, HV), term_variables(DB, BV), vsub(BV, HV, Ex),
    match_goals(DB, B, Idx), locals_ok(Ex, H, B, Idx, DH),
    replace_at(B, Idx, [DH], B1).

lemma_step(Lm, Dir, H-B, H-B1) :-
    lemma_sides(Lm, L0, R0), copy_term(L0-R0, L-R),
    ( Dir == lr -> F = L, T = R ; F = R, T = L ),
    term_variables(F, FV), term_variables(T, TV), vsub(FV, TV, Ex),
    match_goals(F, B, Idx), locals_ok(Ex, H, B, Idx, T),
    replace_at(B, Idx, T, B1).
lemma_sides(lemma(_, L, R), L, R).
lemma_sides(axiom(_, L, R, _), L, R).

% two calls of one predicate with identical first arguments become one
merge_step(C0, H-B1, merge) :-
    copy_term(C0, H-B),
    nth1(I, B, L1), user_lit(L1), nth1(J, B, L2), J > I, user_lit(L2), key(L1, K), key(L2, K),
    arg(1, L1, A1), arg(1, L2, A2), A1 == A2, L1 \== L2,
    unify_with_occurs_check(L1, L2), nth1(J, B, _, B1).

% ---------------------------------------------------------------- search for one clause
% goal: a step clause (a constructor with variables at the induction argument) calls only
% new predicates and builtins
% For an accumulator the step clause must also be a tail call: the definition's outputs are
% passed straight to a call of a new predicate, never computed afterwards by a builtin.
goal(DefKs, Case-Kind, H-B) :-
    arg(Case, H, X),
    (   nonvar(X), term_variables(X, [_|_])
    ->  forall(( member(G, B), user_lit(G) ), ( key(G, K), memberchk(K, DefKs) )),
        (   Kind = tail(OutPos)
        ->  forall(member(P, OutPos), ( arg(P, H, O), \+ ( member(G, B), builtin(G), term_variables(G, GV), vmember(O, GV) ) ))
        ;   true )
    ;   true ).

solve_clause(Spec, Defs, Lemmas, Case, Max, C, C1-Steps) :-
    def_keys(Defs, DK),
    between(0, Max, D), search(Spec, Defs, DK, Lemmas, Case, D, C, C1, Steps), !.

search(_, _, DK, _, Case, _, C, C, []) :- goal(DK, Case, C), !.
search(Spec, Defs, DK, Lemmas, Case, D, C, Cf, [S-C2|Ss]) :-
    D > 0, D1 is D - 1,
    step_op(Defs, Lemmas, C, C1, S),
    normalise(Spec, DK, C1, C2), C2 \== failed,
    search(Spec, Defs, DK, Lemmas, Case, D1, C2, Cf, Ss).

step_op(Defs, _, C, C1, fold(N)) :- member(D, Defs), D = def(DH, _), key(DH, N/_), fold_with(D, C, C1).
step_op(_, Lemmas, C, C1, lemma(N, Dir)) :-
    member(Lm, Lemmas), arg(1, Lm, N), member(Dir, [lr, rl]), lemma_step(Lm, Dir, C, C1).
step_op(_, _, C, C1, merge) :- merge_step(C, C1, merge).

def_keys(Defs, Ks) :- findall(K, ( member(def(H, _), Defs), key(H, K) ), Ks).

% ---------------------------------------------------------------- strategies
strategies([deforest, accumulate, tuple, fuse]).

% eureka(+Strategy, +Spec, +Target, -Def, -Case, -Trace): the definition to transform and the
% argument of its head that holds the induction variable
eureka(deforest, Spec, Target, H-B, Case, [define(H-B)]) :-
    clauses_of(Spec, Target, [H-B]), \+ ( member(G, B), user_lit(G), key(G, Target) ),
    include(user_lit, B, UB), UB = [_, _|_],
    functor(H, _, A), between(1, A, Case), arg(Case, H, X), var(X).
eureka(accumulate, Spec, Target, DH-GB, Case, [eureka(accumulate, DH-GB, generalised(Cons, Cons1))]) :-
    clauses_of(Spec, Target, TCs), member(H-B, TCs),
    nth1(Ir, B, R), user_lit(R), key(R, Target),
    case_pos(Spec, Target, I), arg(I, R, X), var(X),
    term_variables(R, RV), term_variables(H, HV), vsub(RV, HV, Out0), vsub(Out0, [X], Out), Out \== [],
    findall(J, ( nth1(J, B, G), J \== Ir, \+ ( user_lit(G), key(G, Target) ),
                 term_variables(G, GV), member(O, Out), vmember(O, GV) ), Js0),
    sort(Js0, Js), Js \== [],
    maplist({B}/[J, G]>>nth1(J, B, G), Js, Cons),
    generalise(Cons, Out, Cons1, Gen), Gen \== [],
    GB = [R|Cons1],
    others(B, [Ir|Js], Os), term_variables(H-Os, Outside),
    term_variables(GB, BV),
    include({Outside, Gen}/[V]>>( vmember(V, Outside) ; vmember(V, Gen) ), BV, Iface),
    Target = TN/_, atom_concat(TN, '_acc', DN), DH =.. [DN|Iface],
    nth1(Case, Iface, X1), X1 == X,
    % outputs: interface variables of the original clause that the recursive call does not take
    findall(P, ( nth1(P, Iface, V), vmember(V, Outside), \+ vmember(V, RV) ), OutPos),
    nb_setval(fold_kind, DN-tail(OutPos)).
eureka(tuple, Spec, Target, DH-Rs, 1, [eureka(tuple, DH-Rs)]) :-
    clauses_of(Spec, Target, TCs), member(_-B, TCs),
    include({Target}/[G]>>( user_lit(G), key(G, Target) ), B, Rs), Rs = [_, _|_],
    case_pos(Spec, Target, I),
    maplist({I}/[G, A]>>arg(I, G, A), Rs, As),
    As = [A1|_], term_variables(A1, [V]),
    forall(member(A, As), term_variables(A, [V])),
    \+ ( nth1(P, As, A), nth1(Q, As, A2), P < Q, A =@= A2 ),
    term_variables(Rs, RV), vsub(RV, [V], Outs),
    Target = TN/_, atom_concat(TN, '_tup', DN), DH =.. [DN, V|Outs].

% fuse: the recursive call R and the one literal C that consumes its result become one
% predicate, d(X, ...) :- R, C, unfolded on C's case argument X, a variable of the head that R
% does not use. For flat2([L|Ls], F) :- flat2(Ls, F0), app(L, F0, F) this is
% flat2_fuse(L, Ls, F) :- flat2(Ls, F0), app(L, F0, F): the [] case calls flat2 again and the
% [X|Xs] case folds back, so app and the intermediate list F0 disappear.
eureka(fuse, Spec, Target, DH-DB, 1, [eureka(fuse, DH-DB)]) :-
    clauses_of(Spec, Target, TCs), member(H-B, TCs), B = [_, _],
    member(R, B), user_lit(R), key(R, Target),
    member(C, B), C \== R, user_lit(C), \+ key(C, Target), key(C, KC), case_pos(Spec, KC, CI),
    arg(CI, C, X), var(X), term_variables(H, HV), vmember(X, HV),
    term_variables(R, RV), \+ vmember(X, RV),
    term_variables(C, CV), member(O, RV), vmember(O, CV), \+ vmember(O, HV), !,
    term_variables([R, C], BV), include({HV}/[V]>>vmember(V, HV), BV, Iface0),
    exclude(==(X), Iface0, Rest), Iface = [X|Rest],
    Target = TN/_, atom_concat(TN, '_fuse', DN), DH0 =.. [DN|Iface],
    copy_term(DH0-[R, C], DH-DB).                  % the definition shares no variable with Spec

% generalise the consumers: every argument (inside is/2, every subterm of the expression)
% that does not contain an output of the recursive call becomes a fresh variable
generalise([], _, [], []).
generalise([L|Ls], Out, [L1|Ls1], Gen) :-
    (   L = (X is E) -> gen_expr(Out, E, E1, [], G1), L1 = (X is E1)
    ;   L =.. [F|As], foldl(gen_arg(Out), As, As1, [], G1), L1 =.. [F|As1] ),
    generalise(Ls, Out, Ls1, G2), append(G1, G2, Gen).
gen_arg(_, A, A, G, G) :- var(A), !.
gen_arg(Out, A, A, G, G) :- term_variables(A, AV), member(V, AV), vmember(V, Out), !.
gen_arg(_, _, V, G, [V|G]).
gen_expr(Out, E, E, G, G) :- var(E), vmember(E, Out), !.
gen_expr(Out, E, E1, G0, G) :-
    compound(E), term_variables(E, EV), member(V, EV), vmember(V, Out), !,
    E =.. [F|As], foldl(gen_expr(Out), As, As1, G0, G), E1 =.. [F|As1].
gen_expr(_, _, V, G, [V|G]).

% unfold the definition on a literal whose case argument holds the induction variable,
% then search each resulting clause
deforest_on(Spec, H-B, Case, Lemmas, Clauses, Trace) :- deforest_on(Spec, H-B, Case, plain, Lemmas, Clauses, Trace).
deforest_on(Spec, H-B, Case, Kind, Lemmas, Clauses, Trace) :-
    unfolded(Spec, H-B, Case, J, Cs2),
    maplist(solve_clause(Spec, [def(H, B)], Lemmas, Case-Kind, 5), Cs2, Rs),
    pairs_keys_values(Rs, Clauses, StepLists),
    Trace = [unfold(J, Cs2), steps(StepLists)].
unfolded(Spec, H-B, Case, J, Cs2) :-
    arg(Case, H, X), var(X), def_keys([def(H, B)], DK),
    findall(J0-Pr, ( nth1(J0, B, L), user_lit(L), key(L, K), case_pos(Spec, K, I), arg(I, L, Y),
                     term_variables(Y, YV), vmember(X, YV), ( Y == X -> Pr = 1 ; Pr = 0 ) ), JPs),
    sort(2, @=<, JPs, Sorted),            % a constructor around X first: it splits X into cases
    member(J-_, Sorted),
    unfold(Spec, H-B, J, Cs0),
    maplist(normalise(Spec, DK), Cs0, Cs1), exclude(==(failed), Cs1, Cs2).

% spec_to_algorithm(+Spec, +Target, +Lemmas, -Program, -Report)
spec_to_algorithm(Spec, Target, Lemmas, Program, Report) :-
    strategies(Order), spec_to_algorithm(Spec, Target, Lemmas, Order, Program, Report).
% Report = report(Strategy, Trace, LemmasUsed, Attempts, Discovered)
spec_to_algorithm(Spec0, Target, Lemmas, Order, Program, report(S, Trace, Used, Attempts, Disc)) :-
    maplist(sum_first(Target), Spec0, Spec),
    try_order(Order, Spec, Target, Lemmas, 0, S, Program, Trace, Attempts, Disc),
    uses_lemmas(Trace, Used).

% sum_first(+Target, +Clause, -Clause1): in a clause of the target, S is E, where E is a sum
% (with + and -) in which the result R of a recursive call appears once with sign +, becomes
% S is R + Rest, so the accumulate strategy can generalise Rest. On integers this only
% reorders a sum (associativity and commutativity of +). A clause already of that form, or
% not of this kind, is unchanged.
sum_first(Target, H-B, H-B1) :-
    key(H, Target), !,
    foldl(rec_result(Target), B, [], Rs),          % not findall: it would copy the variables
    maplist(sum_first_lit(Rs), B, B1).
sum_first(_, C, C).
rec_result(Target, G, Rs, Rs1) :-
    (   user_lit(G), key(G, Target), G =.. [_|As], last(As, V), var(V) -> Rs1 = [V|Rs] ; Rs1 = Rs ).
sum_first_lit(Rs, X is E, X is E1) :-
    \+ ( E = R0 + _, var(R0), vmember(R0, Rs) ),
    summands(E, +, Ts), select(+(R), Ts, Rest), var(R), vmember(R, Rs), Rest \== [],
    \+ ( member(_-T, Rest), sub_term(Y, T), var(Y), vmember(Y, Rs) ), !,
    rest_expr(Rest, RE), E1 = R + RE.
sum_first_lit(_, G, G).
summands(E, S, Ts) :- nonvar(E), E = A + B, !, summands(A, S, TA), summands(B, S, TB), append(TA, TB, Ts).
summands(E, S, Ts) :- nonvar(E), E = A - B, !, summands(A, S, TA), flip(S, S1), summands(B, S1, TB), append(TA, TB, Ts).
summands(E, S, [T]) :- T =.. [S, E].
flip(+, -). flip(-, +).
rest_expr([T], E) :- !, sign_term(T, E).
rest_expr([T|Ts], E) :- rest_expr(Ts, E0), ( T = +(X) -> E = X + E0 ; T = -(X), E = E0 - X ).
sign_term(+(X), X).
sign_term(-(X), -X).

try_order([S|Ss], Spec, Target, Lemmas, N0, Sf, Program, Trace, N, Disc) :-
    N1 is N0 + 1,
    (   derive(S, Spec, Target, Lemmas, Program, Trace)
    ->  Sf = S, N = N1, Disc = []
    ;   % stuck: conjecture lemmas from the stuck clauses, settle them, retry with the good ones
        findall(St, stuck(S, Spec, Target, St), Sts), append(Sts, Stuck), Stuck \== [],
        discover_lemmas(Spec, Stuck, Lemmas, Found),
        findall(L, ( member(F, Found), ( F = proved(L) ; F = axiom(L) ) ), New), New \== [],
        append(Lemmas, New, Lemmas1),
        derive(S, Spec, Target, Lemmas1, Program, Trace)
    ->  Sf = S, N = N1, Disc = Found
    ;   try_order(Ss, Spec, Target, Lemmas, N1, Sf, Program, Trace, N, Disc)
    ).

derive(S, Spec, Target, Lemmas, Program, Trace) :-
    eureka(S, Spec, Target, DH-DB, Case, Tr0),
    ( S == deforest -> Spec1 = Spec ; Spec1 = [DH-DB|Spec] ),
    ( eureka_kind(DH, Kind) -> true ; Kind = plain ),
    deforest_on(Spec1, DH-DB, Case, Kind, Lemmas, Derived, Tr1), !,
    (   S == deforest -> Program0 = Derived, Tr2 = []
    ;   clauses_of(Spec, Target, TCs),
        maplist(fold_all([def(DH, DB)]), TCs, TCs0),
        maplist(evaluate_call_args(DH), TCs0, TCs1),
        append(TCs1, Derived, Program0), Tr2 = [fold_target(TCs1)] ),
    reachable([Target], Program0, Spec, Program),
    append([Tr0, Tr1, Tr2], Trace).

eureka_kind(DH, Kind) :- functor(DH, DN, _), catch(nb_getval(fold_kind, DN-Kind), _, fail).

% evaluate_call_args(+DefHead, +Clause, -Clause1): folding can leave an arithmetic expression,
% such as H*H, as an argument of the call to the new predicate (the accumulator's start
% value). Compute it first with is/2, so the accumulator is a number: X is E binds X to the
% value of E, so this keeps the least model on numbers.
evaluate_call_args(DH, H-B, H-B1) :- functor(DH, DN, DA), foldl(eval_lit(DN/DA), B, [], B0), B1 = B0.
eval_lit(K, G, Acc, Acc1) :-
    (   key(G, K)
    ->  G =.. [F|As], foldl(eval_arg, As, As1, [], Pre), G1 =.. [F|As1], append([Acc, Pre, [G1]], Acc1)
    ;   append(Acc, [G], Acc1) ).
eval_arg(A, V, Pre, Pre1) :- arith_expr(A), !, append(Pre, [V is A], Pre1).
eval_arg(A, A, Pre, Pre).
arith_expr(E) :- compound(E), functor(E, F, N), memberchk(F/N, [(+)/2, (-)/2, (*)/2, (//)/2, (mod)/2, (-)/1, abs/1, max/2, min/2]).

stuck(S, Spec, Target, Stuck) :-
    eureka(S, Spec, Target, DH-DB, Case, _),
    ( S == deforest -> Spec1 = Spec ; Spec1 = [DH-DB|Spec] ),
    unfolded(Spec1, DH-DB, Case, _, Stuck).

fold_all(Defs, C, C1) :- ( member(D, Defs), fold_with(D, C, C2) -> fold_all(Defs, C2, C1) ; C1 = C ).

uses_lemmas(Trace, Used) :-
    findall(N, ( member(steps(SL), Trace), member(Ss, SL), member(lemma(N, _)-_, Ss) ), U), sort(U, Used).

% clauses of the predicates reachable from Roots; a predicate with new clauses is defined by
% those only, the others by the specification's clauses
reachable(Roots, New, Spec, Program) :-
    findall(K, ( member(H-_, New), key(H, K) ), NK0), sort(NK0, NewKs),
    reach(Roots, New, Spec, NewKs, [], Ks),
    findall(C, ( member(C, New), C = H-_, key(H, K), memberchk(K, Ks) ), P1),
    findall(C, ( member(C, Spec), C = H-_, key(H, K), memberchk(K, Ks), \+ memberchk(K, NewKs) ), P2),
    append(P1, P2, Program).
reach([], _, _, _, Ks, Ks).
reach([K|Rs], New, Spec, NewKs, Seen, Ks) :-
    (   memberchk(K, Seen) -> reach(Rs, New, Spec, NewKs, Seen, Ks)
    ;   ( memberchk(K, NewKs) -> Src = New ; Src = Spec ),
        findall(K2, ( member(H-B, Src), key(H, K), member(G, B), user_lit(G), key(G, K2) ), Ns),
        append(Rs, Ns, Rs1), reach(Rs1, New, Spec, NewKs, [K|Seen], Ks) ).

% ---------------------------------------------------------------- lemmas
% Both sides become predicates over their shared variables and are deforested on the same
% induction variable; proved when the two derived programs are the same up to the name.
prove_lemma(Spec, lemma(N, L0, R0), Result) :-
    copy_term(L0-R0, L-R),
    term_variables(L, LV), term_variables(R, RV), vint(LV, RV, Iface),
    atom_concat(N, '_lhs', LN), atom_concat(N, '_rhs', RN),
    LH =.. [LN|Iface], RH =.. [RN|Iface],
    (   nth1(Case, Iface, _),
        deforest_on(Spec, LH-L, Case, [], LP, _),
        deforest_on(Spec, RH-R, Case, [], RP, _),
        maplist(rename_head(RN, LN), RP, RP1),
        same_clauses(LP, RP1)
    ->  copy_term(LP, LPc), Result = proved(induction_on(Case), LPc)
    ;   Result = not_proved
    ).

rename_head(From, To, H-B, H1-B1) :- ren(From, To, H, H1), maplist(ren(From, To), B, B1).
ren(From, To, G, G1) :- G =.. [F|As], ( F == From -> G1 =.. [To|As] ; G1 = G ).

same_clauses(A, B) :- length(A, N), length(B, N), same_(A, B).
same_([], []).
same_([C|Cs], Bs) :- select(D, Bs, Rest), variant_clause(C, D), !, same_(Cs, Rest).
variant_clause(H1-B1, H2-B2) :- length(B1, N), length(B2, N), permutation(B1, P), (H1-P) =@= (H2-B2), !.

% axioms of integer arithmetic (properties of the integers, not proved here)
axiom(plus_assoc, [S1 is X + Y, S is S1 + Z], [V is Y + Z, S is X + V], int).
axiom(times_assoc, [S1 is X * Y, S is S1 * Z], [V is Y * Z, S is X * V], int).
axiom(max_assoc, [S1 is max(X, Y), S is max(S1, Z)], [V is max(Y, Z), S is max(X, V)], int).

% discover_lemmas(+Spec, +StuckClauses, +Known, -Found): Found holds proved(Lemma),
% axiom(Axiom), refuted(Lemma, CounterExample) or unknown(Lemma) for each new conjecture
discover_lemmas(Spec, Stuck, Known, Found) :-
    findall(C, ( member(_-B, Stuck), conjecture(B, C) ), Cs0),
    dedup_conj(Cs0, Cs),
    exclude({Known}/[C]>>( arg(1, C, N), member(K, Known), arg(1, K, N) ), Cs, New),
    maplist(settle(Spec), New, Found).
% a predicate that chains with itself through a private variable: p(X,Y,W), p(W,Z,R)
conjecture(B, lemma(Name, [L1, L2], [M1, M2])) :-
    nth1(I, B, G1), user_lit(G1), functor(G1, P, 3), nth1(J, B, G2), J \== I, functor(G2, P, 3),
    arg(3, G1, W), var(W), arg(1, G2, W1), W1 == W,
    atom_concat(P, '_assoc', Name),
    L1 =.. [P, X, Y, W0], L2 =.. [P, W0, Z, R], M1 =.. [P, Y, Z, V], M2 =.. [P, X, V, R].
conjecture(B, lemma(Name, [L], [M])) :-
    member(G, B), user_lit(G), functor(G, P, 3),
    atom_concat(P, '_comm', Name), L =.. [P, X, Y, R], M =.. [P, Y, X, R].
conjecture(B, axiom(N, L, R, T)) :-
    member(G1, B), G1 = (S1 is E1), var(S1), compound(E1),
    member(G2, B), G2 \== G1, G2 = (_ is E2), compound(E2), arg(1, E2, A), A == S1,
    functor(E1, Op, 2), functor(E2, Op, 2),
    axiom(N, L, R, T), L = [(_ is E)|_], functor(E, Op, 2).
dedup_conj([], []).
dedup_conj([C|Cs], [C|Rs]) :- arg(1, C, N), exclude({N}/[D]>>arg(1, D, N), Cs, Cs1), dedup_conj(Cs1, Rs).

settle(_, axiom(N, L, R, T), axiom(axiom(N, L, R, T))) :- !.
settle(Spec, lemma(N, L, R), Out) :-
    (   prove_lemma(Spec, lemma(N, L, R), proved(_, _)) -> Out = proved(lemma(N, L, R))
    ;   refute_lemma(Spec, lemma(N, L, R), CE) -> Out = refuted(lemma(N, L, R), CE)
    ;   Out = unknown(lemma(N, L, R)) ).
refute_lemma(Spec, lemma(_, L0, R0), Input) :-
    copy_term(L0-R0, L-R), term_variables(L, LV), term_variables(R, RV), vint(LV, RV, Iface),
    LH =.. [cl|Iface], RH =.. [cr|Iface],
    length(Iface, NA), NI is NA - 1, length(Ins, NI), maplist(=(in(list(any))), Ins), append(Ins, [out], Mode),
    bounded_equal([LH-L|Spec], cl/NA, [RH-R|Spec], cr/NA, Mode, 2, refuted(Input, _, _)).

% ---------------------------------------------------------------- totality
% Mode: list of in(Type) / out. total(+P, +K, +Mode) holds when P has an answer for every
% ground input whose in-arguments have the declared types: the in-argument patterns of K's
% heads cover the types' constructors, every recursive call takes a proper subterm at one
% fixed argument, every call is total in the mode it is called in, every is/2 has bound
% numeric operands, and every output is bound. total/4 also returns P with each checked
% clause body in an order where every call's inputs are bound (the order of a conjunction
% does not change the least model).
total(P, K, TM) :- total(P, K, TM, _).
total(P, K, TM, P1) :-
    b_setval(fold_order, []), b_setval(fold_num, int),
    total_(P, K, TM, [], []), !,
    b_getval(fold_order, Ord), reorder_(P, Ord, [], P1).

% total_(+P, +K, +Modes, +Sub, +Stack): Sub lists the argument positions of K that hold a
% proper subterm of the caller's measured argument; Stack holds frame(K, Modes, M, Sub)
total_(P, K, TM, Sub, Stack) :-
    clauses_of(P, K, Cs), Cs \== [],
    findall(J, nth1(J, TM, in(_)), InJs),
    findall(T, member(in(T), TM), InTs),
    findall(Row, ( member(H-_, Cs), findall(A, ( member(J, InJs), arg(J, H, A) ), Row) ), Rows),
    forall(member(Row, Rows), linear(Row)),
    covers(InTs, Rows),
    measure(Cs, K, TM, M),
    % a loop, not forall/2: forall would undo the recorded body orders
    length(Cs, NC), ( NC =:= 0 -> Ixs = [] ; numlist(1, NC, Ixs) ),
    maplist({P, K, TM, M, Sub, Stack}/[Ix, C]>>clause_total(P, K, TM, M, [frame(K, TM, M, Sub)|Stack], Ix, C), Ixs, Cs).

linear(Row) :- term_variables(Row, Vs), length(Vs, N), aggregate_all(count, ( sub_term(V, Row), var(V) ), N).

% pattern-matrix coverage over the declared constructors
covers([], Rows) :- !, Rows \== [].
covers([T|Ts], Rows) :-
    (   forall(member([P|_], Rows), var(P))
    ->  maplist([[_|R], R]>>true, Rows, Rows1), covers(Ts, Rows1)
    ;   \+ constructor(T, _, _)
    ->  include([[P|_]]>>var(P), Rows, VRows), maplist([[_|R], R]>>true, VRows, Rows1), covers(Ts, Rows1)
    ;   forall(constructor(T, F/A, ATs),
               ( findall(R1, ( member([P|R], Rows), spec_row(P, F, A, R, R1) ), Rows1),
                 append(ATs, Ts, Ts1), covers(Ts1, Rows1) ))
    ).
spec_row(P, _, A, R, R1) :- var(P), !, length(Fs, A), append(Fs, R, R1).
spec_row(P, F, A, R, R1) :- functor(P, F, A), P =.. [_|As], append(As, R, R1).

% an in-argument at which every recursive call takes a proper subterm of the head's argument
measure(Cs, K, TM, M) :-
    (   \+ ( member(_-B, Cs), member(G, B), user_lit(G), key(G, K) ) -> M = none
    ;   nth1(M, TM, in(_)),
        forall(( member(H-B, Cs), member(G, B), user_lit(G), key(G, K) ),
               ( arg(M, H, HA), arg(M, G, GA), var(GA), nonvar(HA), sub_term(S, HA), S == GA )), !
    ).

clause_total(P, K, TM, M, Stack, Ix, H-B) :-
    head_env(H, TM, Env0, Bound0),
    length(B, N), ( N =:= 0 -> Is = [] ; numlist(1, N, Is) ), permutation(Is, PIs),
    maplist({B}/[I, G]>>nth1(I, B, G), PIs, BP),
    body_total(BP, H, P, K, TM, M, Stack, Env0, Bound0, Bound), !,
    forall(( nth1(J, TM, out), arg(J, H, A) ), ( term_variables(A, AV), forall(member(V, AV), vmember(V, Bound)) )),
    b_getval(fold_order, O0), b_setval(fold_order, [K-Ix-PIs|O0]).

head_env(H, TM, Env, Bound) :-
    findall(J-T, nth1(J, TM, in(T)), JTs),
    foldl({H}/[J-T, E0, E]>>( arg(J, H, A), bind_types(A, T, E0, E) ), JTs, [], Env),
    pairs_keys(Env, Bound).
bind_types(A, T, E0, [A-T|E0]) :- var(A), !.
bind_types(A, T, E0, E) :- constructor(T, F/N, ATs), functor(A, F, N), !,
    A =.. [_|As], pairs_of(As, ATs, Ps), foldl([X-Y, Ea, Eb]>>bind_types(X, Y, Ea, Eb), Ps, E0, E).
bind_types(A, _, E0, E) :- term_variables(A, Vs), foldl([V, Ea, [V-any|Ea]]>>true, Vs, E0, E).

env_type(Env, V, T) :- member(W-T0, Env), W == V, !, T = T0.

body_total([], _, _, _, _, _, _, _, Bound, Bound).
body_total([L|Ls], H, P, K, TM, M, Stack, Env0, Bound0, Bound) :-
    (   L = (X is E)
    ->  var(X), \+ vmember(X, Bound0),
        term_variables(E, EV),
        forall(member(V, EV), ( vmember(V, Bound0), env_type(Env0, V, T), type_le(T, num) )),
        (   forall(member(V, EV), ( env_type(Env0, V, T), type_le(T, int) )) -> XT = int
        ;   XT = num, b_setval(fold_num, num) ),
        Env1 = [X-XT|Env0], Bound1 = [X|Bound0]
    ;   builtin(L) -> fail                % a test can fail, so a clause with one is not total
    ;   key(L, Q), L =.. [_|Args],
        maplist(arg_mode(Env0, Bound0), Args, QTM),
        mode_args(Args, QTM, out, Outs),
        maplist(var, Outs), sort(Outs, SO), length(SO, NO), length(Outs, NO),
        (   Q == K -> M \== none, maplist(mode_le, QTM, TM)
        ;   back_edge(P, H, K, Q, Args, QTM, Stack) -> true
        ;   \+ memberchk(frame(Q, _, _, _), Stack),
            sub_positions(H, TM, Args, Sub), total_(P, Q, QTM, Sub, Stack) ),
        out_types(QTM, Args, 1, P, Q, OTs),          % (no findall: it would copy the variables)
        append(OTs, Env0, Env1),
        term_variables(L, LV), append(LV, Bound0, Bound1)
    ),
    body_total(Ls, H, P, K, TM, M, Stack, Env1, Bound1, Bound).

% sub_positions(+Head, +Modes, +CallArgs, -Sub): pairs J-I where the call's argument J is a
% variable that is a proper subterm of the head's input argument I
sub_positions(H, TM, Args, Sub) :-
    findall(J-I, ( nth1(I, TM, in(_)), arg(I, H, HA), nonvar(HA),
                   nth1(J, Args, A), var(A), sub_term(S, HA), S == A ), Sub).

% back_edge: K was called from Q with its argument Pp a proper subterm of Q's input argument
% I; K's own recursive calls keep Pp unchanged; and this call of Q passes K's argument Pp at
% I. Then the pair (size of Q's argument I, K's measure) decreases lexicographically around
% the cycle Q -> K -> ... -> K -> Q, so Q may be assumed total here (well-founded induction),
% at modes no more instantiated than those Q is being proved for.
back_edge(P, H, K, Q, Args, QTM, [frame(K, _, _, SubK), frame(Q, TMQ, _, _)|_]) :-
    member(Pp-I, SubK), nth1(I, Args, A), var(A), arg(Pp, H, HP), HP == A,
    preserved(P, K, Pp), maplist(mode_le, QTM, TMQ).
preserved(P, K, Pp) :-
    forall(( member(H-B, P), key(H, K), member(G, B), user_lit(G), key(G, K) ),
           ( arg(Pp, H, X), arg(Pp, G, Y), var(X), X == Y )).

out_types([], [], _, _, _, []).
out_types([M|Ms], [A|As], J, P, Q, OTs) :- J1 is J + 1,
    ( M == out -> out_type(P, Q, J, T), OTs = [A-T|R] ; OTs = R ), out_types(Ms, As, J1, P, Q, R).

arg_mode(Env, Bound, A, M) :-
    term_variables(A, Vs),
    (   forall(member(V, Vs), vmember(V, Bound)) -> infer_type(A, Env, T), M = in(T)
    ;   M = out ).
mode_le(in(S), in(T)) :- type_le(S, T).
mode_le(out, out).
out_type(P, Q, J, T) :- ( slot_type(P, Q, J, T0) -> T = T0 ; T = any ).

% infer_type(+Term, +Env, -Type): the most specific declared type of a bound term
infer_type(A, Env, T) :- var(A), !, ( env_type(Env, A, T) -> true ; T = any ).
infer_type(A, _, int) :- integer(A).
infer_type(A, Env, T) :-
    nonvar(A), functor(A, F, N), constructor_any(T, F/N, ATs), A =.. [_|As],
    pairs_of(As, ATs, Ps),
    forall(member(X-AT, Ps), ( infer_type(X, Env, XT), ( var(AT) -> AT = XT ; type_le(XT, AT) -> true ; AT = XT ) )),
    maplist({Env}/[X-AT]>>( var(AT) -> infer_type(X, Env, AT) ; true ), Ps),
    term_variables(T, TV), maplist(=(any), TV).
infer_type(A, _, any) :- nonvar(A).

reorder_([], _, _, []).
reorder_([H-B|Cs], Ord, Seen, [H-B1|Cs1]) :-
    key(H, K), aggregate_all(count, member(K, Seen), N0), Ix is N0 + 1,
    (   memberchk(K-Ix-PIs, Ord) -> maplist({B}/[I, G]>>nth1(I, B, G), PIs, B1) ; B1 = B ),
    reorder_(Cs, Ord, [K|Seen], Cs1).

% ---------------------------------------------------------------- functionality
% at most one answer per ground input: heads do not overlap on the inputs, every call is
% functional in the mode it is called in, and every output is bound
functional(P, K, M) :- functional_(P, K, M, []).
functional_(_, K, M, Seen) :- member(K-M0, Seen), M0 == M, !.
functional_(P, K, M, Seen) :-
    clauses_of(P, K, Cs), Cs \== [],
    \+ ( nth1(I, Cs, C1), nth1(J, Cs, C2), I < J, inputs_overlap(C1, C2, M) ),
    forall(member(C, Cs), clause_fun(P, M, [K-M|Seen], C)).

in_args(H, M, As) :- H =.. [_|Args], mode_args(Args, M, in, As).
out_args(H, M, As) :- H =.. [_|Args], mode_args(Args, M, out, As).
mode_args([], [], _, []).
mode_args([A|As], [Md|Ms], W, Out) :-
    ( ( W == out -> Md == out ; Md \== out ) -> Out = [A|Out1] ; Out = Out1 ), mode_args(As, Ms, W, Out1).
inputs_overlap(H1-_, H2-_, M) :- in_args(H1, M, A1), in_args(H2, M, A2), \+ \+ unify_with_occurs_check(A1, A2).

clause_fun(P, M, Seen, H-B) :-
    in_args(H, M, InAs), term_variables(InAs, Bound0),
    foldl(lit_fun(P, Seen), B, Bound0, Bound),
    out_args(H, M, OutAs), term_variables(OutAs, OV),
    forall(member(V, OV), vmember(V, Bound)).
lit_fun(_, _, (X is E), Bound0, Bound) :- !,
    term_variables(E, EV), forall(member(V, EV), vmember(V, Bound0)),
    term_variables(X, XV), append(XV, Bound0, Bound).
lit_fun(_, _, L, Bound, Bound) :- builtin(L), !, term_variables(L, V), forall(member(X, V), vmember(X, Bound)).
lit_fun(P, Seen, L, Bound0, Bound) :-
    key(L, Q), L =.. [_|Args],
    maplist({Bound0}/[A, Md]>>( term_variables(A, Vs), ( forall(member(V, Vs), vmember(V, Bound0)) -> Md = in ; Md = out ) ),
            Args, QM),
    functional_(P, Q, QM, Seen),
    term_variables(L, LV), append(LV, Bound0, Bound).

% ---------------------------------------------------------------- argument types of answers
% slot_type(+P, +K, +I, ?T): every answer of K in P has a value of type T at argument I
% (induction on derivation height). With T unbound the type is inferred first.
slot_type(P, K, I, T) :-
    (   var(T) -> once(slot_candidate(P, K, I, [], T0)), T0 \== any, T = T0 ; true ),
    slot_check(P, K, I, T, []).
slot_candidate(P, K, I, Seen, T) :-
    \+ memberchk(K-I, Seen),
    clauses_of(P, K, Cs), member(H-B, Cs), arg(I, H, X),
    term_candidate(X, B, P, [K-I|Seen], T).
term_candidate(X, _, _, _, int) :- integer(X), !.
term_candidate(X, B, _, _, int) :- var(X), member(G, B), G = (Y is _), Y == X, !.
term_candidate(X, B, P, S, T) :- var(X), !,
    member(G, B), user_lit(G), arg(J, G, Y), Y == X, key(G, Q), slot_candidate(P, Q, J, S, T).
term_candidate(X, _, _, _, T) :- infer_type(X, [], T0), T0 \== any, generalise_type(T0, T).
generalise_type(T0, T) :- T0 =.. [F|As], length(As, N), length(Vs, N), T1 =.. [F|Vs],
    ( N > 0, constructor_any(T1, _, _) -> maplist(=(any), Vs), T = T1 ; T = T0 ).

slot_check(_, K, I, T, Seen) :- member(K-I-T0, Seen), type_le(T0, T), !.
slot_check(P, K, I, T, Seen) :-
    clauses_of(P, K, Cs), Cs \== [],
    forall(member(H-B, Cs), ( arg(I, H, X), has_type(X, T, B, P, [K-I-T|Seen]) )).
has_type(_, T, _, _, _) :- T == any, !.
has_type(X, T, _, _, _) :- integer(X), ( type_le(int, T) ; T == nat, X == 0 ), !.
has_type(X, T, B, _, _) :- var(X), member(G, B), G = (Y is _), Y == X, !, type_le(int, T).
has_type(X, T, B, P, S) :- var(X), !,
    member(G, B), user_lit(G), arg(J, G, Y), Y == X, key(G, Q), slot_check(P, Q, J, T, S), !.
has_type(X, T, B, P, S) :- constructor(T, F/N, ATs), functor(X, F, N), !,
    X =.. [_|As], pairs_of(As, ATs, Ps), forall(member(A-AT, Ps), has_type(A, AT, B, P, S)).

% ---------------------------------------------------------------- verification
% verify(+Spec, +Program, +Target, +Mode, -Verdict)
verify(Spec, Prog, K, Mode, verdict(Tot, Fun, Typ, IntArith, Ordered)) :-
    (   total(Prog, K, Mode, Ordered) -> Tot = total(yes), b_getval(fold_num, NumT)
    ;   Tot = total(no), Ordered = Prog, NumT = unknown ),
    ( NumT == int -> IntArith = integer_arithmetic(yes) ; IntArith = integer_arithmetic(no) ),
    maplist([X, Y]>>( X = in(_) -> Y = in ; Y = out ), Mode, FM),
    ( functional(Spec, K, FM) -> Fun = functional(yes) ; Fun = functional(no) ),
    (   forall(( nth1(J, Mode, in(T)), T \== any ), slot_type(Spec, K, J, T))
    ->  Typ = typed_answers(yes) ; Typ = typed_answers(no) ).

% ---------------------------------------------------------------- evaluation
answers(P, G, As) :- findall(G, solve(P, [G], 0, _), As0), sort(As0, As).
steps(P, G, N, As) :- findall(G-N0, solve(P, [G], 0, N0), L), pairs_keys_values(L, As, Ns), sum_list(Ns, N).

% cost(+P, +G, -Steps, -MaxGoals): resolution steps and the largest number of pending goals
% (the interpreter's stack) for the first answer
cost(P, G, Steps, Max) :- once(solve_c(P, [G], 0, Steps, 0, Max)).
solve_c(_, [], N, N, M, M).
solve_c(P, [G|Gs], N0, N, M0, M) :-
    N0 < 2000000, N1 is N0 + 1,
    (   builtin(G) -> catch(G, _, fail), Gs1 = Gs
    ;   member(C, P), copy_term(C, H-B), unify_with_occurs_check(H, G), append(B, Gs, Gs1) ),
    length(Gs1, L), M1 is max(M0, L),
    solve_c(P, Gs1, N1, N, M1, M).

solve(_, [], N, N).
solve(P, [G|Gs], N0, N) :-
    N0 < 2000000, N1 is N0 + 1,
    (   builtin(G) -> catch(G, _, fail), Gs1 = Gs
    ;   member(C, P), copy_term(C, H-B), unify_with_occurs_check(H, G), append(B, Gs, Gs1) ),
    solve(P, Gs1, N1, N).

% values of a type up to a size
values(any, _, [a, b]) :- !.
values(int, _, [0, 1, 2, 5]) :- !.
values(num, _, [0, 1, 2, 5]) :- !.
values(nat, D, Vs) :- !, numlist(0, D, Ns), maplist(peano, Ns, Vs).
values(list(E), D, Vs) :- !, values(E, D, Es),
    findall(L, ( between(0, D, Len), length(L, Len), maplist({Es}/[X]>>member(X, Es), L) ), Vs).
values(tree(E), D, Vs) :- !, values(E, D, Es), trees(D, Es, Vs).
peano(0, 0) :- !.
peano(N, s(P)) :- N1 is N - 1, peano(N1, P).
trees(0, _, [leaf]) :- !.
trees(D, Es, Vs) :- D1 is D - 1, trees(D1, Es, Ts),
    findall(node(L, X, R), ( member(L, Ts), member(X, Es), member(R, Ts) ), Ns), append([leaf], Ns, Vs0),
    sort(Vs0, Vs).

% bounded_equal(+P1, +K1, +P2, +K2, +Mode, +Size, -Result)
bounded_equal(P1, K1, P2, K2, Mode, Size, Result) :-
    K1 = N1/A, K2 = N2/A,
    findall(J, nth1(J, Mode, in(_)), InJs),
    findall(Vs, ( member(J, InJs), nth1(J, Mode, in(T)), values(T, Size, Vs) ), Sets),
    aggregate_all(count, maplist(member, _, Sets), Total),
    (   maplist(member, Tuple, Sets),
        length(Args, A), place(InJs, Tuple, Args),
        G1 =.. [N1|Args], G2 =.. [N2|Args],
        answers(P1, G1, S1), answers(P2, G2, S2b), maplist(ren(N2, N1), S2b, S2), sort(S2, S2s),
        S1 \== S2s
    ->  Result = refuted(input(Tuple), first(S1), second(S2b))
    ;   Result = equal_on(Total)
    ).
place([], [], _).
place([J|Js], [V|Vs], Args) :- nth1(J, Args, V), place(Js, Vs, Args).

% ---------------------------------------------------------------- learning the strategy
% features of a target's specification
features(Spec, Target, Fs) :-
    clauses_of(Spec, Target, Cs),
    findall(F, feature(Cs, Target, F), Fs0), sort(Fs0, Fs).
feature(Cs, K, conjunctive) :-
    Cs = [_-B], include(user_lit, B, U), U = [_, _|_], \+ ( member(G, B), user_lit(G), key(G, K) ).
feature(Cs, K, result_used_after_call) :-
    member(H-B, Cs), member(R, B), user_lit(R), key(R, K),
    term_variables(R, RV), term_variables(H, HV), vsub(RV, HV, Out), member(O, Out),
    member(G, B), G \== R, \+ ( user_lit(G), key(G, K) ), term_variables(G, GV), vmember(O, GV).
feature(Cs, K, calls_on_related_arguments) :-
    member(_-B, Cs), include({K}/[G]>>( user_lit(G), key(G, K) ), B, [R1, R2|_]),
    arg(1, R1, A1), arg(1, R2, A2), A1 \== A2, term_variables(A1, [V]), term_variables(A2, [W]), V == W.
feature(Cs, K, two_recursive_calls) :-
    member(_-B, Cs), include({K}/[G]>>( user_lit(G), key(G, K) ), B, [_, _|_]).
feature(Cs, _, arithmetic) :- member(_-B, Cs), member(G, B), compound(G), functor(G, is, 2).

% learn_strategies(+Examples, -Rules): Examples = [Features-SucceededStrategies]. For each
% strategy, sequential covering finds conjunctions of feature literals (F or not(F)) that hold
% for examples where it succeeded and for none where it failed.
learn_strategies(Examples, Rules) :-
    strategies(Ss),
    findall(S-Rule, ( member(S, Ss), learn_one(S, Examples, Rule) ), Rules).
learn_one(S, Examples, Rule) :-
    partition({S}/[_-Ok]>>memberchk(S, Ok), Examples, Pos0, Neg0),
    pairs_keys(Pos0, Pos), pairs_keys(Neg0, Neg),
    ( Pos == [] -> Rule = never ; cover(Pos, Neg, Conjs) -> Rule = any_of(Conjs) ; Rule = never ).
cover([], _, []) :- !.
cover(Pos, Neg, [C|Cs]) :-
    all_literals(Pos, Neg, Lits),
    % the shortest conjunction that excludes every negative; among those, the one that covers
    % the most positives, then the one with the fewest negated features, then the first in
    % the fixed order of the features
    between(1, 3, N),
    findall(k(Cnt, NegN, _)-C0,
            ( length(C0, N), subseq_of(C0, Lits), \+ ( member(F, Neg), holds_all(C0, F) ),
              aggregate_all(count, ( member(F, Pos), holds_all(C0, F) ), Cnt), Cnt > 0,
              aggregate_all(count, member(not(_), C0), NN), NegN is -NN ), Cands0),
    Cands0 \== [], !,
    length(Cands0, NC), numlist(1, NC, Is), maplist([k(A, B, _)-X, I, k(A, B, O)-X]>>(O is -I), Cands0, Is, Cands),
    max_member(_-C, Cands),
    exclude({C}/[F]>>holds_all(C, F), Pos, Rest),
    cover(Rest, Neg, Cs).
all_literals(Pos, Neg, Lits) :-
    append(Pos, Neg, All), append(All, Fs0), sort(Fs0, Fs),
    findall(L, ( member(F, Fs), ( L = F ; L = not(F) ) ), Lits).
subseq_of([], _).
subseq_of([X|Xs], [X|Ys]) :- subseq_of(Xs, Ys).
subseq_of(Xs, [_|Ys]) :- subseq_of(Xs, Ys).
holds_all(C, Fs) :- forall(member(L, C), holds(L, Fs)).
holds(not(F), Fs) :- !, \+ memberchk(F, Fs).
holds(F, Fs) :- memberchk(F, Fs).

% choose_order(+Rules, +Features, -Order): strategies whose learned rule holds first, then the
% rest in the default order
choose_order(Rules, Fs, Order) :-
    strategies(Ss),
    include({Rules, Fs}/[S]>>( memberchk(S-any_of(Cs), Rules), member(C, Cs), holds_all(C, Fs) ), Ss, First),
    subtract(Ss, First, Rest), append(First, Rest, Order).

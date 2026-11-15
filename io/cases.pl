% The predicates whose inputs and outputs are recorded in io/ios.txt (see io/ios_engine.pl).
:- ios_engine:load_repo('prolog/optimise/optimise').
:- ios_engine:load_repo('prolog/s2a/s2a').
:- ios_engine:load_repo('prolog/s2a/s2a2_bridge').
:- ios_engine:load_repo('prolog/ir/ir').
:- ios_engine:load_repo('prolog/proof/proof_checker').
:- use_module(library(readutil)).

io_title('mnns').

% s2a2, s2a2_learn_apply, s2a2_derive and check_proof need S2A2 (github.com/luciangreen/S2A2)
% beside this repository or at $S2A2_HOME; CI fetches it.
io_cases([optimise_file, s2a, s2a2, s2a2_learn_apply, s2a2_derive, check_proof]).

% Small programs to optimise, made from parts.
program(K, Text) :-
    num(K, 1, 1, 6, Kind),
    pick(K, 2, [num, item, val, n], F),
    pick_n(K, 3, 5, [1, 2, 3, 4, 5, 7, 9], Ns),
    maplist([N, L]>>format(string(L), "~w(~w).", [F, N]), Ns, Ls), atomic_list_concat(Ls, '\n', Facts),
    template(Kind, F, Rules),
    format(string(Text), "~w~n~w~n", [Facts, Rules]).

template(1, F, R) :- format(string(R), "values(Xs) :- findall(X, ~w(X), Xs).", [F]).
template(2, F, R) :- format(string(R), "total(T) :- findall(X, ~w(X), Xs), sum_list(Xs, T).", [F]).
template(3, _, "sum([], 0).\nsum([X|Xs], S) :- sum(Xs, S0), S is S0 + X.").
template(4, _, "len([], 0).\nlen([_|T], N) :- len(T, N0), N is N0 + 1.").
template(5, F, R) :- format(string(R), "doubled(Ys) :- findall(Y, (~w(X), Y is X * 2), Ys).", [F]).
template(6, _, "app([], L, L).\napp([H|T], L, [H|R]) :- app(T, L, R).").

% Examples for spec to algorithm: inputs and the outputs wanted.
spec(K, Spec) :-
    num(K, 4, 1, 4, Kind),
    pick_n(K, 5, 3, [[5,6], [7,8], [1,2], [3,9], [4,4]], Pairs),
    sort(Pairs, Ps),
    maplist(spec_pair(Kind), Ps, Spec).
spec_pair(1, [A,B], [[input, [['A', [A,B]]]], [output, [['B', [B,A]]]]]).
spec_pair(2, [A,B], [[input, [['A', A]]], [output, [['B', B]]]]).
spec_pair(3, [A,B], [[input, [['A', A], ['B', B]]], [output, [['C', S]]]]) :- S is A + B.
spec_pair(4, [A,_], [[input, [['A', A]]], [output, [['B', D]]]]) :- D is A * 2.

io_input(optimise_file, K, [Program]) :- program(K, Program).
io_input(s2a, K, [Name, Spec, Options]) :- pick(K, 6, [probe_a, probe_b, swap_probe], Name), spec(K, Spec), pick(K, 7, [[], [allow_table(true)]], Options).

% optimises a program file; the report line and the clauses written (variables named in order)
io_run(optimise_file, [Program], [report(Line), emitted(Emitted)]) :-
    In = '/tmp/mnns_ios_in.pl', Out = '/tmp/mnns_ios_out.pl',
    setup_call_cleanup(open(In, write, S), write(S, Program), close(S)),
    with_output_to(string(_), mnn_optimise:optimise_file(In, Out, Report)),
    mnn_optimise:optimise_report_line(Report, Line),
    ( exists_file(Out) -> setup_call_cleanup(open(Out, read, R), clauses(R, Emitted), close(R)), delete_file(Out) ; Emitted = none ).

clauses(R, Cs) :-
    read_term(R, T, []),
    ( T == end_of_file -> Cs = []
    ; numbervars(T, 0, _), format(string(C), "~W", [T, [quoted(true), numbervars(true), portray(false), spacing(next_argument)]]),
      Cs = [C | Rest], clauses(R, Rest) ).
io_run(s2a, [Name, Spec, Options], Result) :- with_output_to(string(_), mnn_s2a:s2a(Name, Spec, Options, Result)).

% ---- The S2A2 bridge ----

% A program in mnns's IR as clauses to read: variables named in order.
clauses_of(Program, Texts) :-
    mnn_ir:ir_to_prolog(Program, Terms),
    exclude([T]>>(T = (:- _)), Terms, Cs),
    maplist(clause_text, Cs, Texts).
clause_text(T0, Text) :-
    copy_term(T0, T), numbervars(T, 0, _),
    format(string(Text), "~W", [T, [quoted(true), numbervars(true), portray(false), spacing(next_argument)]]).

% Runs Name(In, Out) of a program in mnns's IR on each input (in a scratch module).
run_program(Program, Name, Inputs, Outputs) :-
    mnn_ir:ir_to_prolog(Program, Terms0),
    exclude([T]>>(T = (:- _)), Terms0, Terms),
    setup_call_cleanup(
        forall(member(T, Terms), assertz(ios_scratch:T)),
        findall(Out, ( member(In, Inputs), G =.. [Name, In, O],
                       ( catch(call_with_depth_limit(ios_scratch:G, 100000, _), _, fail) -> Out = O ; Out = none ) ), Outputs),
        forall(member(T, Terms), ( T = (H :- _) -> retractall(ios_scratch:H) ; retractall(ios_scratch:T) ))).

% Lists of numbers for examples and samples.
lists(K, Salt, Ls) :-
    findall(L, ( between(1, 4, I), S is Salt * 7 + I, num(K, S, 0, 4, N), length(L, N),
                 foldl([X, J0, J]>>(S2 is S * 11 + J0, num(K, S2, -3, 9, X), J is J0 + 1), L, 0, _) ), Ls0),
    sort(Ls0, Ls).

% What each kind of list function gives.
kind_out(reverse, L, R) :- reverse(L, R).
kind_out(evens, L, R) :- include([X]>>(0 is X mod 2), L, R).
kind_out(odds, L, R) :- include([X]>>(1 is X mod 2), L, R).
kind_out(len, L, N) :- length(L, N).
kind_out(sum, L, S) :- sum_list(L, S).
kind_out(double_each, L, R) :- maplist([X, Y]>>(Y is 2 * X), L, R).
kind_out(dropmax, L, R) :- ( L = [] -> R = [] ; max_list(L, M), d(L, M, R) ).
d([], _, []).
d([X|Xs], M, R) :- ( X == M -> R = R1 ; R = [X|R1] ), d(Xs, M, R1).

% References to prove the program against (right, or wrong on purpose).
reference(evens, [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 0 -> R = [X|R1] ; R = R1 ), r(Xs, R1))]).
reference(odds, [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 1 -> R = [X|R1] ; R = R1 ), r(Xs, R1))]).
reference(dropmax, [r([], []), (r([X|Xs], R) :- max_list([X|Xs], M), dd([X|Xs], M, R)),
                    dd([], _, []), (dd([X|Xs], M, R) :- ( X == M -> R = R1 ; R = [X|R1] ), dd(Xs, M, R1))]).

io_input(s2a2, K, [Kind, Spec, Options]) :-
    pick(K, 8, [reverse, evens, len, odds, sum, double_each, dropmax, evens], Kind),
    lists(K, 9, Ls0), ( Kind == dropmax -> exclude(==([]), Ls0, Ls) ; Ls = Ls0 ),
    findall([[input, [['A', L]]], [output, [['B', O]]]], ( member(L, Ls), kind_out(Kind, L, O) ), Spec),
    pick(K, 10, [none, evens, odds, dropmax], RefKind),
    ( RefKind \== none, memberchk(Kind, [evens, odds, dropmax]) -> reference(RefKind, Ref), Options = [ga(false), time_limit(8), reference(Ref, r)]
    ; Options = [ga(false), time_limit(8)] ).

% s2a2/4: who solved it, the program, the proof, and mnns's checker on the proof
io_run(s2a2, [Kind, Spec, Options], Result) :-
    with_output_to(string(_), mnn_s2a2:s2a2(Kind, Spec, Options, P)),
    (   P = mnn_program(_, meta(Meta, _), _, Proof, trace(Trace))
    ->  clauses_of(P, Cs),
        ( Meta = s2a2_io_synth(_, How) -> By = s2a2(How) ; functor(Meta, By0, _), By = By0 ),
        exclude([T]>>(T = s2a2_reference(_)), Trace, Trace1),
        (   memberchk(s2a2_reference(Ref), Trace)
        ->  mnn_proof_checker:check_proof(P, Ref, Proof, Check)
        ;   Check = no_reference
        ),
        findall(L, member([[input, [['A', L]]], _], Spec), Ins0), append(Ins0, [[1, 2, 3, 4, 5, 6]], Ins),
        Result = [solved_by(By), program(Cs), proof(Proof), trace(Trace1), check(Check), runs_on(Ins, Outs)],
        run_program(P, Kind, Ins, Outs)
    ;   Result = P
    ).

% ---- Learning and applying an optimisation algorithm ----

ir(Name, Clauses, IR) :- mnn_s2a2:ir_of(Name, Clauses, ios, [], proof([]), IR).

% Before/after pairs: unfold a wrapper (keep it), or delete it too (over-general).
pair(keep, Top, Base, Wrap, Xs, pair(B, A, [Top/1])) :-
    facts(Base, Xs, Fs),
    H1 =.. [Top, X1], W1 =.. [Wrap, X1], H2 =.. [Wrap, X2], G2 =.. [Base, X2],
    H3 =.. [Top, X3], G3 =.. [Base, X3],
    append(Fs, [(H2 :- G2), (H1 :- W1)], Before), append(Fs, [(H2 :- G2), (H3 :- G3)], After),
    ir(Top, Before, B), ir(Top, After, A).
pair(drop, Top, Base, Wrap, Xs, pair(B, A, [Top/1])) :-
    facts(Base, Xs, Fs),
    H1 =.. [Top, X1], W1 =.. [Wrap, X1], H2 =.. [Wrap, X2], G2 =.. [Base, X2],
    H3 =.. [Top, X3], G3 =.. [Base, X3],
    append(Fs, [(H2 :- G2), (H1 :- W1)], Before), append(Fs, [(H3 :- G3)], After),
    ir(Top, Before, B), ir(Top, After, A).
facts(F, Xs, Fs) :- findall(T, ( member(X, Xs), T =.. [F, X] ), Fs).

io_input(s2a2_learn_apply, K, [Style, Pairs, Edges]) :-
    pick(K, 11, [keep, keep, drop], Style),
    pick_n(K, 12, 3, [red, blue, green], Cs0), sort(Cs0, Cs),
    pick_n(K, 13, 3, [s1, s2, s3], Ss0), sort(Ss0, Ss),
    num(K, 14, 1, 2, NP),
    Pairs0 = [col-colour-q-Cs, big-size-s-Ss], length(Pairs, NP), append(Pairs, _, Pairs0),
    pick_n(K, 15, 4, [a-b, b-c, c-d, a-c, d-a], Es0), sort(Es0, Edges).

% learns from the pairs, applies to conn/2 over the edges: the algorithm, the new program,
% S2A2's prover's verdict, the proof and mnns's checker on it
io_run(s2a2_learn_apply, [Style, Pairs, Edges], Result) :-
    maplist([Top-Base-Wrap-Xs, Pr]>>pair(Style, Top, Base, Wrap, Xs, Pr), Pairs, Prs),
    with_output_to(string(_), mnn_s2a2:s2a2_learn(Prs, [], Alg)),
    findall(edge(U, V), member(U-V, Edges), Fs),
    append(Fs, [(e(U1, V1) :- edge(U1, V1)), (conn(U2, V2) :- e(U2, V2))], Cs),
    ir(conn, Cs, P),
    with_output_to(string(_), mnn_s2a2:s2a2_apply(Alg, P, [conn/2], [], R)),
    R = mnn_program(_, _, _, Proof, trace(Trace)),
    clauses_of(R, Out),
    ( Proof = proof([_|_]) -> mnn_proof_checker:check_proof(R, P, Proof, Check) ; Check = no_proof ),
    copy_term(Alg, Alg1), numbervars(Alg1, 0, _),
    Result = [algorithm(Alg1), program(Out), trace(Trace), proof(Proof), check(Check)].

% ---- Deriving a faster program ----

spec_program(sum, [in(list(int)), out], [sum([], 0), (sum([H|T], S) :- sum(T, S1), S is S1 + H)]).
spec_program(len, [in(list(any)), out], [len([], 0), (len([_|T], N) :- len(T, N0), N is N0 + 1)]).
spec_program(flat2, [in(list(list(any))), out], [flat2([], []), (flat2([L|Ls], F) :- flat2(Ls, F0), app(L, F0, F)),
                                                 app([], A, A), (app([X|Xs], B, [X|C]) :- app(Xs, B, C))]).
spec_program(rev, [in(list(any)), out], [rev([], []), (rev([H|T], R) :- rev(T, R0), app(R0, [H], R)),
                                         app([], A, A), (app([X|Xs], B, [X|C]) :- app(Xs, B, C))]).
spec_program(sumsq, [in(list(int)), out], [sumsq([], 0), (sumsq([H|T], S) :- sumsq(T, S1), S is S1 + H * H)]).

io_input(s2a2_derive, K, [Name, Bound, Samples]) :-
    pick(K, 16, [sum, flat2, len, rev, sumsq], Name),
    num(K, 17, 2, 3, Bound),
    lists(K, 18, Ls),
    ( Name == flat2 -> findall(G, ( append(A, B, Ls), A \== [], G = [A, B] ), Gs0), Gs0 = [_|_], length(Gs0, NG), M is min(2, NG), length(Samples, M), append(Samples, _, Gs0)
    ; Samples = Ls ).

% derives with S2A2's fold.pl: the strategy and verdict, the program, mnns's checker on the
% proof, and both programs run on the samples
io_run(s2a2_derive, [Name, Bound, Samples], Result) :-
    spec_program(Name, Mode, Clauses), ir(Name, Clauses, Spec),
    with_output_to(string(_), mnn_s2a2:s2a2_derive(Spec, Mode, [bound(Bound)], R)),
    (   R = mnn_program(_, _, _, Proof, trace([s2a2_fold(Strategy, Lemmas, Total, Functional, _, Bounded)]))
    ->  clauses_of(R, Cs),
        mnn_proof_checker:check_proof(R, Spec, Proof, Check),
        run_program(Spec, Name, Samples, Want), run_program(R, Name, Samples, Got),
        ( Lemmas = lemmas(Ls) -> true ; Ls = Lemmas ),
        Result = [strategy(Strategy), lemmas(Ls), Total, Functional, Bounded, program(Cs), proof(Proof), check(Check), spec_gives(Want), derived_gives(Got)]
    ;   Result = R
    ).

% ---- mnns's checker on S2A2 proofs given for the wrong program ----

io_input(check_proof, K, [What, N]) :-
    pick(K, 19, [fold_changed, fold_not_derived, edb_changed, edb_syntactic, edb_same], What),
    num(K, 20, 1, 3, N).

io_run(check_proof, [What, N], Verdict) :- check_case(What, N, P, Orig, Proof), mnn_proof_checker:check_proof(P, Orig, Proof, Verdict).

fold_proof(proof([proof_step(1, fold_derivation, [], equivalent(domain(mode([in(list(int)), out])), modes([in(list(int)), out])))])).
check_case(fold_changed, N, Wrong, Spec, Proof) :-
    ir(sum, [sum([], 0), (sum([H|T], S) :- sum(T, S1), S is S1 + H)], Spec),
    ir(sum, [sum([], 0), (sum([H1|T1], S2) :- sum(T1, S3), S2 is S3 + H1 + N)], Wrong), fold_proof(Proof).
check_case(fold_not_derived, _, Spec, Spec, Proof) :-
    ir(sum, [sum([], 0), (sum([H|T], S) :- sum(T, S1), S is S1 + H)], Spec), fold_proof(Proof).
check_case(edb_changed, N, Wrong, P, proof([proof_step(1, edb_equivalence, [], equivalent(domain(edb([edge/2], Cs)), modes(targets([conn/2]))))])) :-
    length(Cs, N), append(Cs, _, [a, b, c]),
    ir(conn, [edge(a,b), (e(U,V) :- edge(U,V)), (conn(U1,V1) :- e(U1,V1))], P),
    ir(conn, [edge(a,b), (e(U2,V2) :- edge(U2,V2)), (conn(U3,V3) :- edge(V3,U3))], Wrong).
check_case(edb_same, N, Q, P, proof([proof_step(1, edb_equivalence, [], equivalent(domain(edb([edge/2], Cs)), modes(targets([conn/2]))))])) :-
    length(Cs, N), append(Cs, _, [a, b, c]),
    ir(conn, [edge(a,b), (e(U,V) :- edge(U,V)), (conn(U1,V1) :- e(U1,V1))], P),
    ir(conn, [edge(a,b), (e(U2,V2) :- edge(U2,V2)), (conn(U3,V3) :- edge(U3,V3))], Q).
check_case(edb_syntactic, N, Q, P, proof([proof_step(1, edb_equivalence, [], equivalent(domain(all), modes(targets([r/1]))))])) :-
    findall((r(Z) :- a(Z)), between(1, N, _), Extra),
    append([(r(X1) :- a(X1)), (r(Y) :- a(Y), b(Y))], Extra, Cs),
    ir(r, Cs, P), ir(r, [(r(X2) :- a(X2))], Q).

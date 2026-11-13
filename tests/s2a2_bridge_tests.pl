:- begin_tests(mnn_s2a2, [condition(mnn_s2a2:s2a2_available)]).

% These tests need S2A2 (github.com/luciangreen/S2A2) beside this repository, or at
% $S2A2_HOME. Without it they are skipped; s2a2/4 then gives s2a/4's results.

:- use_module('../prolog/s2a/s2a2_bridge').
:- use_module('../prolog/ir/ir').

spec(Exs, Spec) :- findall([[input, [['A', I]]], [output, [['B', O]]]], member(I-O, Exs), Spec).

% emit the program, load it, and run Name on each input
run_emitted(Program, Name, Inputs, Outputs) :-
    Program = mnn_program(Module, _, _, _, _),
    setup_call_cleanup(
        ( tmp_file_stream(text, File, S), close(S) ),
        ( mnn_ir:emit_program(Program, File), load_files(File, [silent(true)]),
          findall(O, ( member(I, Inputs), G =.. [Name, I, O0], ( call(Module:G) -> O = O0 ; O = none ) ), Outputs) ),
        ( unload_file(File), delete_file(File) )).

test(cases_s2a_solves_are_unchanged) :-
    spec([box(red, [5,6])-[5,6], box(blue, [7,8])-[7,8]], S),
    mnn_s2a:s2a(p, S, [], P0), mnn_s2a2:s2a2(p, S, [], P1),
    assertion(P0 =@= P1),
    spec([1-5, 2-7, 4-11], A),
    mnn_s2a:s2a(a, A, [], Q0), mnn_s2a2:s2a2(a, A, [], Q1),
    assertion(Q0 =@= Q1).

test(reverse_from_s2a2_generalises) :-
    spec([[1,2,3]-[3,2,1], [4,5,6,7]-[7,6,5,4]], S),
    mnn_s2a:s2a(reverse, S, [], no_algorithm(_)),
    mnn_s2a2:s2a2(reverse, S, [], P),
    P = mnn_program(mnn_s2a2_reverse, meta(s2a2_io_synth(reverse, expression), _), _, proof([]),
                    trace([s2a2_io_synth(reverse, expression, examples_reproduced(2))])),
    run_emitted(P, reverse, [[1,2], [8], []], Outs),
    assertion(Outs == [[2,1], [8], []]).

test(nested_predicates_from_s2a2) :-
    spec([[[1,3,5],[5,3,2]]-[[3,5],[5,3]], [[7,9],[4]]-[[9],[]]], S),
    mnn_s2a2:s2a2(dropmin_each, S, [], P),
    P = mnn_program(_, meta(s2a2_io_synth(dropmin_each, map), _), Preds, _, _),
    length(Preds, NP), assertion(NP >= 3),
    run_emitted(P, dropmin_each, [[[4,2,9],[3]], [[]]], Outs),
    assertion(Outs == [[[4,9],[]], [[]]]).

test(mnns_proof_against_a_reference) :-
    spec([[1,2,3,4]-[2,4], [5,6]-[6], [7]-[], [-2,1]-[-2]], S),
    Ref = [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 0 -> R = [X|R1] ; R = R1 ), r(Xs, R1))],
    mnn_s2a2:s2a2(evens, S, [reference(Ref, r)], P),
    P = mnn_program(_, _, _, Proof, trace([_, s2a2_reference(RefIR)])),
    assertion(Proof == proof([proof_step(1, induction_equivalence, [], equivalent(domain(types([list(int), any])), modes(all)))])),
    mnn_proof_checker:check_proof(P, RefIR, Proof, accepted).

test(the_mnns_checker_refuses_the_proof_for_a_different_program) :-
    spec([[1,2,3,4]-[2,4], [5,6]-[6], [7]-[], [-2,1]-[-2]], S),
    Ref = [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 0 -> R = [X|R1] ; R = R1 ), r(Xs, R1))],
    mnn_s2a2:s2a2(evens, S, [reference(Ref, r)], mnn_program(_, _, _, Proof, trace([_, s2a2_reference(RefIR)]))),
    spec([[1,2,3,4]-[1,3], [5,6]-[5], [8]-[], [-1,2]-[-1]], S2),
    mnn_s2a2:s2a2(odds, S2, [], P2),
    mnn_proof_checker:check_proof(P2, RefIR, Proof, rejected(_)).

test(wrong_reference_is_not_proved) :-
    spec([[1,2,3,4]-[2,4], [5,6]-[6], [7]-[], [-2,1]-[-2]], S),
    Ref = [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 1 -> R = [X|R1] ; R = R1 ), r(Xs, R1))],
    mnn_s2a2:s2a2(evens, S, [reference(Ref, r)], P),
    P = mnn_program(_, _, _, proof([]), trace([_, s2a2_proof(r, not_proved)])).

test(invariant_proof_for_drop_the_maximum) :-
    spec([[3,1,2]-[1,2], [7,9,8]-[7,8], [5,6,4]-[5,4]], S),
    Ref = [r([], []), (r([X|Xs], R) :- max_list([X|Xs], M), d([X|Xs], M, R)),
           d([], _, []), (d([X|Xs], M, R) :- ( X == M -> R = R1 ; R = [X|R1] ), d(Xs, M, R1))],
    mnn_s2a2:s2a2(dropmax, S, [reference(Ref, r)], P),
    P = mnn_program(_, _, _, proof([_]), trace([_, s2a2_reference(RefIR)])),
    P = mnn_program(_, _, _, Proof, _),
    mnn_proof_checker:check_proof(P, RefIR, Proof, accepted).

ir(Name, Clauses, IR) :- mnn_s2a2:ir_of(Name, Clauses, test, [], proof([]), IR).

% the pairs of S2A2's loop2 family: a caller calls a wrapper; after, it calls the generator
test(learn_and_apply_an_optimisation_algorithm) :-
    ir(col, [colour(red), colour(blue), (q(X) :- colour(X)), (col(X1) :- q(X1))], B1),
    ir(col, [colour(red), colour(blue), (q(X2) :- colour(X2)), (col(X3) :- colour(X3))], A1),
    ir(big, [size(s1), size(s2), size(s3), (s(Y) :- size(Y)), (big(Y1) :- s(Y1))], B2),
    ir(big, [size(s1), size(s2), size(s3), (s(Y2) :- size(Y2)), (big(Y3) :- size(Y3))], A2),
    mnn_s2a2:s2a2_learn([pair(B1, A1, [col/1]), pair(B2, A2, [big/1])], [], Alg),
    assertion(Alg = algorithm([rule(unfold, _)])),
    ir(conn, [edge(a,b), edge(b,c), (e(U,V) :- edge(U,V)), (conn(U1,V1) :- e(U1,V1))], P),
    mnn_s2a2:s2a2_apply(Alg, P, [conn/2], [], R),
    R = mnn_program(_, _, Preds, proof([]), trace([s2a2_apply([step(_)]), s2a2_prover(Verdict)])),
    memberchk(mnn_pred(conn/2, _, _, [mnn_clause(_, conn(C1, C2), edge(D1, D2), _)], _), Preds),
    assertion(C1-C2 == D1-D2),
    assertion(Verdict = proved(_)).

% too few distinctions in the pairs: deleting the wrapper too gives an unconditional
% del_clause, which S2A2's prover refutes on a new program
test(an_over_general_algorithm_is_refuted_by_the_prover) :-
    ir(col, [colour(red), colour(blue), (q(X) :- colour(X)), (col(X1) :- q(X1))], B1),
    ir(col, [colour(red), colour(blue), (col(X2) :- colour(X2))], A1),
    ir(big, [size(s1), size(s2), size(s3), (s(Y) :- size(Y)), (big(Y1) :- s(Y1))], B2),
    ir(big, [size(s1), size(s2), size(s3), (big(Y2) :- size(Y2))], A2),
    mnn_s2a2:s2a2_learn([pair(B1, A1, [col/1]), pair(B2, A2, [big/1])], [], Alg),
    ir(conn, [edge(a,b), edge(b,c), (e(U,V) :- edge(U,V)), (conn(U1,V1) :- e(U1,V1))], P),
    mnn_s2a2:s2a2_apply(Alg, P, [conn/2], [], R),
    R = mnn_program(_, _, _, _, trace([_, s2a2_prover(refuted(_, _, _))])).

test(derive_an_accumulator_program) :-
    ir(sum, [sum([], 0), (sum([H|T], S) :- sum(T, S1), S is S1 + H)], Spec),
    mnn_s2a2:s2a2_derive(Spec, [in(list(int)), out], [], R),
    R = mnn_program(_, _, Preds, proof([]), trace([s2a2_fold(accumulate, _, total(yes), functional(yes), _, bounded(equal_on(_)))])),
    assertion(memberchk(mnn_pred(sum_acc/3, _, _, _, _), Preds)),
    run_emitted(R, sum, [[1,2,3], []], Outs),
    assertion(Outs == [6, 0]).

test(derive_flatten_by_fusion) :-
    ir(flat2, [flat2([], []), (flat2([L|Ls], F) :- flat2(Ls, F0), app(L, F0, F)),
               app([], A, A), (app([X|Xs], B, [X|C]) :- app(Xs, B, C))], Spec),
    mnn_s2a2:s2a2_derive(Spec, [in(list(list(any))), out], [bound(3)], R),
    R = mnn_program(_, _, _, _, trace([s2a2_fold(fuse, _, total(yes), functional(yes), _, _)])),
    run_emitted(R, flat2, [[[1,2],[3]]], Outs),
    assertion(Outs == [[1,2,3]]).

test(table_only_when_asked_and_nothing_generalises) :-
    spec([a-b, c-d], S),
    mnn_s2a2:s2a2(t, S, [ga(false)], no_algorithm(_)),
    mnn_s2a2:s2a2(t, S, [ga(false), allow_table(true)], P),
    P = mnn_program(_, _, _, _, trace([s2a_table(t, examples_reproduced(2))])).

test(problems_with_the_spec_are_not_sent_to_s2a2) :-
    mnn_s2a2:s2a2(x, [], [], no_algorithm(empty_spec)),
    spec([1-2, 1-3], C), mnn_s2a2:s2a2(x, C, [], no_algorithm(conflicting_examples(_))),
    spec([1-2, 2-3], O), mnn_s2a2:s2a2(x, O, [bad], no_algorithm(invalid_options)).

test(without_s2a2_the_result_is_s2a_s) :-
    spec([[1,2,3]-[3,2,1], [4,5,6,7]-[7,6,5,4]], S),
    mnn_s2a:s2a(reverse, S, [], R0),
    mnn_s2a2:s2a2(reverse, S, [s2a2_home('/nonexistent/S2A2')], R1),
    assertion(R0 =@= R1).

:- end_tests(mnn_s2a2).

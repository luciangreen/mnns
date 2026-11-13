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

test(proof_against_a_reference_in_the_trace) :-
    spec([[1,2,3,4]-[2,4], [5,6]-[6], [7]-[], [-2,1]-[-2]], S),
    Ref = [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 0 -> R = [X|R1] ; R = R1 ), r(Xs, R1))],
    mnn_s2a2:s2a2(evens, S, [reference(Ref, r)], P),
    P = mnn_program(_, _, _, proof([]), trace([_, s2a2_proof(r, proved(Steps))])),
    assertion(memberchk(pair(evens/2, r/2, induction(1), none), Steps)).

test(wrong_reference_is_not_proved) :-
    spec([[1,2,3,4]-[2,4], [5,6]-[6], [7]-[], [-2,1]-[-2]], S),
    Ref = [r([], []), (r([X|Xs], R) :- ( X mod 2 =:= 1 -> R = [X|R1] ; R = R1 ), r(Xs, R1))],
    mnn_s2a2:s2a2(evens, S, [reference(Ref, r)], P),
    P = mnn_program(_, _, _, _, trace([_, s2a2_proof(r, not_proved)])).

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

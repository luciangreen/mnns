:- begin_tests(mnn_loop2).

:- use_module('../prolog/ir/ir').
:- use_module('../prolog/loop2/loop2').

test(converts_ground_fact_generator_and_preserves_answer_order, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         num(3),
         (numbers(Values) :- findall(X, num(X), Values))],
        Converted, loop2_report([conversion(findall_to_fold, _, _)])),
    assertion(Converted = mnn_program(_, _, Predicates, _, _)),
    assertion(member(mnn_pred(mnn_loop2_1/2, _, _, _, generated(loop2)),
                     Predicates)),
    run_converted(Converted, numbers(Values), [[[1, 2, 3]]]).

test(generates_distinct_helpers_for_multiple_findalls, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         colour(red),
         colour(blue),
         (numbers(Values) :- findall(X, num(X), Values)),
         (red_colours(Values) :- findall(x, colour(red), Values))],
        Converted, loop2_report(Conversions)),
    assertion(Conversions =
              [conversion(findall_to_fold, helper(mnn_loop2_1/2), _),
               conversion(findall_to_fold, helper(mnn_loop2_2/2), _)]),
    run_converted(Converted, numbers(_), [[[1, 2]]]),
    run_converted(Converted, red_colours(_), [[[x]]]).

test(leaves_filtered_generators_unchanged, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         num(3),
         (numbers(Values) :-
             findall(X, (num(X), X > 1), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(numbers/1, _, _,
                           [mnn_clause(_, _, findall(_, (_, _), _), _)],
                           original),
                  Predicates)),
    run_converted(Converted, numbers(_), [[[2, 3]]]).

test(leaves_rule_generators_and_unrelated_cut_unchanged, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         (positive(X) :- num(X), X > 1),
         positive(0),
         (stop :- !),
         (numbers(Values) :- findall(X, positive(X), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(mnn_pred(positive/1, _, _, Clauses, original),
                     Predicates)),
    assertion(length(Clauses, 2)),
    assertion(member(mnn_pred(stop/0, _, _,
                              [mnn_clause(_, _, !, _)],
                              original),
                     Predicates)),
    run_converted(Converted, numbers(_), [[[2, 0]]]).

test(leaves_builtin_generators_unchanged, [nondet]) :-
    with_converted_program(
        [between(1, 2, 1),
         between(1, 2, 2),
         (values(Values) :- findall(X, between(1, 2, X), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(values/1, _, _,
                           [mnn_clause(_, _, findall(_, between(1, 2, _), _), _)],
                           original),
                  Predicates)).

test(skips_generated_names_already_in_use, [nondet]) :-
    with_converted_program(
        [num(1),
         (mnn_loop2_1(Left, Right) :- Left = Right),
         (numbers(Values) :- findall(X, num(X), Values))],
        Converted, loop2_report(
                       [conversion(findall_to_fold,
                                   helper(mnn_loop2_2/2), _)])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(mnn_pred(mnn_loop2_1/2, _, _, _, original),
                     Predicates)),
    assertion(member(mnn_pred(mnn_loop2_2/2, _, _, _, generated(loop2)),
                     Predicates)).

with_converted_program(Terms, Converted, Report) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, Terms),
          mnn_ir:parse_program(Source, Original),
          mnn_loop2:convert_program(Original, Converted, Report)
        ),
        delete_file(Source)).

run_converted(Program, Goal, Answers) :-
    mnn_ir:ir_to_prolog(Program, Terms),
    term_variables(Goal, Variables),
    setup_call_cleanup(
        assert_program_terms(Terms, References),
        findall(Variables, call(Goal), Answers),
        maplist(erase, References)).

assert_program_terms([], []).
assert_program_terms([Term|Terms], [Reference|References]) :-
    assertz(Term, Reference),
    assert_program_terms(Terms, References).

temporary_source(File) :-
    tmp_file_stream(text, File, Stream),
    close(Stream).

write_source(File, Terms) :-
    open(File, write, Stream),
    write_terms(Stream, Terms),
    close(Stream).

write_terms(_, []).
write_terms(Stream, [Term|Terms]) :-
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n'),
    write_terms(Stream, Terms).

:- end_tests(mnn_loop2).

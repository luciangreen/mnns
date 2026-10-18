:- begin_tests(mnn_loop2).

:- use_module('../prolog/ir/ir').
:- use_module('../prolog/loop2/loop2').
:- use_module('../prolog/runner/sandbox_runner').

test(converts_ground_fact_generator_and_preserves_answer_order) :-
    with_converted_program(
        [num(1),
         num(2),
         num(3),
         (numbers(Values) :- findall(X, num(X), Values))],
        Converted, loop2_report([conversion(findall_to_fold, _, _)])),
    assertion(Converted = mnn_program(_, _, Predicates, _, _)),
    assertion(member(mnn_pred(mnn_loop2_1/2, _, _, _, generated(loop2)),
                     Predicates)),
    run_converted(Converted, numbers(Values), [Values]),
    assertion(Values == [1, 2, 3]).

test(generates_distinct_helpers_for_multiple_findalls) :-
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
    run_converted(Converted, numbers(Numbers), [Numbers]),
    assertion(Numbers == [1, 2]),
    run_converted(Converted, red_colours(Colours), [Colours]),
    assertion(Colours == [x]).

test(leaves_filtered_generators_unchanged) :-
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
                           [mnn_clause(_, _, findall(_, conj(_, _), _), _)],
                           original),
                  Predicates)),
    run_converted(Converted, numbers(Values), [Values]),
    assertion(Values == [2, 3]).

test(skips_generated_names_already_in_use) :-
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
    setup_call_cleanup(
        temporary_source(Source),
        ( mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(Source, Goal, [], answers(Answers))
        ),
        delete_file(Source)).

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

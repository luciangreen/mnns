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

test(converts_supported_arithmetic_filters, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         num(3),
         (numbers(Values) :-
             findall(X, (num(X), X > 1), Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                        side_conditions(finite_ground_facts(3),
                                        safe_arithmetic_filters(1),
                                        deterministic_loop))])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(mnn_pred(mnn_loop2_1/2, _, _, _, generated(loop2)),
                     Predicates)),
    run_converted(Converted, numbers(Values), [[[2, 3]]]).

test(leaves_unsupported_or_unbound_filters_unchanged, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         allowed(2),
         (using_user_filter(Values) :-
             findall(X, (num(X), allowed(X)), Values)),
         (using_unbound_limit(Values, Limit) :-
             findall(X, (num(X), X > Limit), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(using_user_filter/1, _, _,
                           [mnn_clause(_, _, findall(_, (_, _), _), _)],
                           original),
                  Predicates)),
    assertion(member(
                  mnn_pred(using_unbound_limit/2, _, _,
                           [mnn_clause(_, _, findall(_, (_, _), _), _)],
                           original),
                  Predicates)).

test(leaves_unsupported_rule_generators_and_unrelated_cut_unchanged, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         (positive(X) :- num(X), append([X], [], [2])),
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

test(converts_finite_multiclause_rule_generator_in_clause_order, [nondet]) :-
    with_converted_program(
        [num(1),
         num(2),
         num(3),
         (positive(X) :- num(X), X > 1),
         positive(0),
         (numbers(Values) :- findall(X, positive(X), Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                        side_conditions(finite_acyclic_rules(3),
                                        safe_arithmetic_filters(0),
                                        deterministic_loop))])),
    run_converted(Converted, numbers(Values), [[[2, 3, 0]]]).

test(leaves_recursive_and_unbound_rule_generators_unchanged, [nondet]) :-
    with_converted_program(
        [(recursive(X) :- recursive(X)),
         (unbound(X) :- X > _Limit),
         (recursive_values(Values) :-
             findall(X, recursive(X), Values)),
         (unbound_values(Values) :-
             findall(X, unbound(X), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(recursive_values/1, _, _,
                           [mnn_clause(_, _,
                                       findall(_, recursive(_), _), _)],
                           original),
                  Predicates)),
    assertion(member(
                  mnn_pred(unbound_values/1, _, _,
                           [mnn_clause(_, _,
                                       findall(_, unbound(_), _), _)],
                           original),
                  Predicates)).

test(leaves_unsupported_builtin_generators_unchanged, [nondet]) :-
    with_converted_program(
        [(values(Values) :- findall(X, append(X, [3], [1, 2, 3]), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(values/1, _, _,
                           [mnn_clause(_, _, findall(_, append(_, _, _), _), _)],
                           original),
                  Predicates)).

test(converts_ground_between_generator, [nondet]) :-
    with_converted_program(
        [(values(Values) :- findall(X, between(1, 3, X), Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                       side_conditions(finite_ground_between(3),
                                       safe_arithmetic_filters(0),
                                       deterministic_loop))])),
    run_converted(Converted, values(Values), [[[1, 2, 3]]]).

test(converts_ground_member_generator_and_preserves_duplicates, [nondet]) :-
    with_converted_program(
        [(values(Values) :-
              findall(X, member(X, [3, 1, 3]), Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                                       side_conditions(finite_ground_member(3),
                                                       safe_arithmetic_filters(0),
                                                       deterministic_loop))])),
    run_converted(Converted, values(Values), [[[3, 1, 3]]]).

test(converts_member_with_arithmetic_filter_and_template, [nondet]) :-
    with_converted_program(
        [(values(Values) :-
              findall(pair(X), (member(X, [1, 3, 4]), X > 2), Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                                       side_conditions(finite_ground_member(3),
                                                       safe_arithmetic_filters(1),
                                                       deterministic_loop))])),
    run_converted(Converted, values(Values), [[[pair(3), pair(4)]]]).

test(converts_nth0_and_preserves_indices_and_duplicates, [nondet]) :-
    with_converted_program(
        [(values(Values) :-
              findall(pair(Index, Value),
                      nth0(Index, [a, b, a], Value),
                      Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                        side_conditions(finite_ground_nth0(3),
                                                       safe_arithmetic_filters(0),
                                                       deterministic_loop))])),
    run_converted(Converted, values(Values),
                  [[[pair(0, a), pair(1, b), pair(2, a)]]]).

test(converts_nth1_with_bound_arguments_and_filter, [nondet]) :-
    with_converted_program(
        [(indices(Indices) :-
              findall(Index,
                      (nth1(Index, [a, b, a], a), Index > 1),
                      Indices))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                        side_conditions(finite_ground_nth1(3),
                                                       safe_arithmetic_filters(1),
                                                       deterministic_loop))])),
    run_converted(Converted, indices(Indices), [[[3]]]).

test(converts_nth0_with_bound_index, [nondet]) :-
    with_converted_program(
        [(values(Values) :- findall(Value, nth0(1, [a, b], Value), Values))],
        Converted, loop2_report(
                       [conversion(findall_to_fold, helper(mnn_loop2_1/2), _)])),
    run_converted(Converted, values(Values), [[[b]]]).

test(leaves_member_with_variable_list_unchanged, [nondet]) :-
    with_converted_program(
        [(values(List, Values) :-
              findall(X, member(X, List), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(values/2, _, _,
                                          [mnn_clause(_, _, findall(_, member(_, _), _), _)],
                                          original),
                  Predicates)).

test(leaves_nth_generators_with_variable_lists_unchanged, [nondet]) :-
    with_converted_program(
        [(values(List, Values) :-
              findall(X, nth0(_, List, X), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(values/2, _, _,
                          [mnn_clause(_, _, findall(_, nth0(_, _, _), _), _)],
                          original),
                  Predicates)).

test(converts_between_with_arithmetic_filters_and_template, [nondet]) :-
    with_converted_program(
        [(values(Values) :-
              findall(pair(X), (between(1, 4, X), X > 2), Values))],
        Converted,
        loop2_report(
            [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                       side_conditions(finite_ground_between(4),
                                       safe_arithmetic_filters(1),
                                       deterministic_loop))])),
    run_converted(Converted, values(Values), [[[pair(3), pair(4)]]]).

test(converts_empty_and_singleton_between_ranges, [nondet]) :-
    with_converted_program(
        [(empty(Values) :- findall(X, between(5, 2, X), Values)),
         (singleton(Values) :- findall(X, between(7, 7, X), Values))],
        Converted, loop2_report(Conversions)),
    assertion(Conversions =
              [conversion(findall_to_fold, helper(mnn_loop2_1/2),
                         side_conditions(finite_ground_between(0),
                                         safe_arithmetic_filters(0),
                                         deterministic_loop)),
               conversion(findall_to_fold, helper(mnn_loop2_2/2),
                         side_conditions(finite_ground_between(1),
                                         safe_arithmetic_filters(0),
                                         deterministic_loop))]),
    run_converted(Converted, empty(Values), [[[]]]),
    run_converted(Converted, singleton(Values), [[[7]]]).

test(leaves_non_ground_or_oversized_between_unchanged, [nondet]) :-
    with_converted_program(
        [(variable_bounds(Values, Low, High) :-
              findall(X, between(Low, High, X), Values)),
         (oversized(Values) :- findall(X, between(1, 10001, X), Values))],
        Converted, loop2_report([])),
    Converted = mnn_program(_, _, Predicates, _, _),
    assertion(member(
                  mnn_pred(variable_bounds/3, _, _,
                          [mnn_clause(_, _, findall(_, between(_, _, _), _), _)],
                          original),
                  Predicates)),
    assertion(member(
                  mnn_pred(oversized/1, _, _,
                          [mnn_clause(_, _, findall(_, between(_, _, _), _), _)],
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

:- begin_tests(mnn_aioc_test_runner).

:- use_module('../prolog/aioc/test_runner').

test(accepts_matching_ordered_answers_and_duplicates) :-
    answer_program(candidate, [a, b, a], Candidate),
    answer_program(original, [a, b, a], Original),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original, [test_case(answer, answer(_Value))], [],
        [test_result(answer, passed)]).

test(reports_answer_order_mismatch) :-
    answer_program(candidate, [b, a], Candidate),
    answer_program(original, [a, b], Original),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original, [test_case(answer, answer(_Value))], [],
        [test_result(answer, failed(answer_mismatch([[a], [b]], [[b], [a]])))]).

test(identical_failure_is_a_pass) :-
    answer_program(candidate, [a], Candidate),
    answer_program(original, [a], Original),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original, [test_case(missing, answer(missing))], [],
        [test_result(missing, passed)]).

test(reports_inconclusive_when_answer_limit_is_reached) :-
    answer_program(candidate, [a, b, c], Candidate),
    answer_program(original, [a, b, c], Original),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original, [test_case(answer, answer(_Value))],
        [max_answers(2)],
        [test_result(answer, inconclusive(answer_limit_exceeded(2)))]).

test(reports_candidate_execution_error) :-
    answer_program(candidate, [a], Candidate),
    answer_program(original, [a], Original),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original,
        [test_case(error, throw(error(test_failure, _)))], [],
        [test_result(error, failed(candidate_error(_)))]).

test(rejects_unknown_options,
     [throws(error(domain_error(option, unknown_option), _))]) :-
    answer_program(candidate, [a], Candidate),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Candidate, [], [unknown_option], _).

answer_program(Name, Values,
               mnn_program(Name, meta(Name, Events), [Predicate],
                           proof([]), trace([]))) :-
    answer_clauses(Values, 1, Name, Clauses, Events),
    Predicate = mnn_pred(answer/1, ['?'], [any], Clauses, original).

answer_clauses([], _, _, [], []).
answer_clauses([Value|Values], Id, Name,
               [mnn_clause(Id, answer(Value), true, source(Name, Id))|Clauses],
               [clause(Id)|Events]) :-
    NextId is Id + 1,
    answer_clauses(Values, NextId, Name, Clauses, Events).

:- end_tests(mnn_aioc_test_runner).

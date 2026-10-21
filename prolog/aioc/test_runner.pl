:- module(mnn_aioc_test_runner,
          [ compare_programs/5
          ]).

:- use_module(library(error)).
:- use_module(library(option)).
:- use_module('../ir/ir').
:- use_module('../runner/sandbox_runner').

compare_programs(Candidate, Original, TestCases, Options, Results) :-
    must_be(list, TestCases),
    maplist(validate_test_case, TestCases),
    validate_options(Options, MaxAnswers, RunOptions),
    setup_call_cleanup(
        temporary_program_file(Candidate, CandidateFile),
        setup_call_cleanup(
            temporary_program_file(Original, OriginalFile),
            maplist(compare_test_case(CandidateFile, OriginalFile,
                                      RunOptions, MaxAnswers),
                    TestCases, Results),
            delete_temporary_file(OriginalFile)),
        delete_temporary_file(CandidateFile)).

validate_test_case(test_case(Name, Goal)) :-
    !,
    must_be(atom, Name),
    (   callable(Goal)
    ->  true
    ;   throw(error(type_error(callable, Goal), _))
    ).
validate_test_case(TestCase) :-
    throw(error(domain_error(test_case, TestCase), _)).

validate_options(Options, MaxAnswers, RunOptions) :-
    must_be(list, Options),
    maplist(validate_option, Options),
    option(max_answers(MaxAnswers), Options, 100),
    must_be(integer, MaxAnswers),
    (   MaxAnswers > 0
    ->  true
    ;   throw(error(domain_error(positive_integer, MaxAnswers), _))
    ),
    MaxAnswersWithSentinel is MaxAnswers + 1,
    exclude(max_answers_option, Options, OtherOptions),
    RunOptions = [max_answers(MaxAnswersWithSentinel)|OtherOptions].

validate_option(Option) :-
    (   known_option(Option)
    ->  true
    ;   throw(error(domain_error(option, Option), _))
    ).

known_option(max_answers(_)).
known_option(time_limit(_)).

max_answers_option(max_answers(_)).

temporary_program_file(Program, File) :-
    tmp_file(mnn_aioc_test_program, TemporaryBase),
    atom_concat(TemporaryBase, '.pl', File),
    mnn_ir:emit_program(Program, File).

delete_temporary_file(File) :-
    catch(delete_file(File), _, true).

compare_test_case(CandidateFile, OriginalFile, Options, MaxAnswers,
                  test_case(Name, Goal), Result) :-
    copy_term(Goal, CandidateGoal),
    copy_term(Goal, OriginalGoal),
    run_test_program(CandidateFile, CandidateGoal, Options, CandidateOutcome),
    run_test_program(OriginalFile, OriginalGoal, Options, OriginalOutcome),
    compare_test_outcomes(Name, MaxAnswers, CandidateOutcome, OriginalOutcome,
                          Result).

run_test_program(File, Goal, Options, Outcome) :-
    (   catch(( mnn_sandbox_runner:run_program(
                    File, Goal, Options, answers(Answers))
              -> Outcome = completed(Answers)
              ;  Outcome = completed([])
              ),
              Error,
              Outcome = error(Error))
    ->  true
    ;   Outcome = completed([])
    ).

compare_test_outcomes(Name, MaxAnswers, completed(CandidateAnswers),
                      completed(OriginalAnswers), Result) :-
    !,
    (   length(CandidateAnswers, CandidateCount),
        length(OriginalAnswers, OriginalCount),
        ( CandidateCount > MaxAnswers
        ; OriginalCount > MaxAnswers
        )
    ->  Result = test_result(Name, inconclusive(answer_limit_exceeded(MaxAnswers)))
    ;   CandidateAnswers =@= OriginalAnswers
    ->  Result = test_result(Name, passed)
    ;   Result = test_result(
                    Name,
                    failed(answer_mismatch(OriginalAnswers, CandidateAnswers)))
    ).
compare_test_outcomes(Name, _, error(Error), _,
                      test_result(Name, failed(candidate_error(Error)))) :-
    !.
compare_test_outcomes(Name, _, _, error(Error),
                      test_result(Name, failed(original_error(Error)))).

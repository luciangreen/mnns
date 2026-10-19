:- begin_tests(mnn_detlog_transform).

:- use_module('../prolog/ir/ir').
:- use_module('../prolog/detlog/detlog_transform').
:- use_module('../prolog/runner/sandbox_runner').

test(compiles_pure_once_and_preserves_answers, [nondet]) :-
    Original = mnn_program(
                   sample, meta(sample, [clause(1)]),
                   [mnn_pred(choose/1, ['?'], [any],
                             [mnn_clause(1, choose(Value),
                                         once(disj(Value = a, Value = b)),
                                         source(sample, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Original, Transformed,
        detlog_transform_report(
            [compiled_once(choose/1, 1, disj(_, _))])),
    Transformed = mnn_program(
                      sample, meta(sample, [clause(1)]),
                      [mnn_pred(choose/1, ['?'], [any],
                                [mnn_clause(1, choose(TransformedValue),
                                            ite(disj(TransformedValue = a,
                                                     TransformedValue = b),
                                                true, fail),
                                            source(sample, 1))],
                                original)],
                      proof([]), trace([])),
    run_ir(Original, choose(Value0), OriginalAnswers),
    run_ir(Transformed, choose(Value1), TransformedAnswers),
    assertion(OriginalAnswers == [[a]]),
    assertion(TransformedAnswers == OriginalAnswers).

test(keeps_unsupported_once_and_transforms_supported_sibling) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(mixed/1, ['?'], [any],
                            [mnn_clause(1, mixed(Value),
                                        conj(once(Value = a), once(!)),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(mixed/1, _, _,
                                    [mnn_clause(_, mixed(Value),
                                                conj(ite(Value = a, true, fail),
                                                     once(!)),
                                                _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(mixed/1, 1, _),
             kept_once(mixed/1, 1, unsupported_goal(!))])).

test(keeps_user_predicate_once_unchanged) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(caller/0, [], [],
                            [mnn_clause(1, caller, once(helper), source(sample, 1))],
                            original),
                   mnn_pred(helper/0, [], [],
                            [mnn_clause(2, helper, true, source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed,
        detlog_transform_report(
            [kept_once(caller/0, 1, unsupported_goal(helper))])),
    assertion(Transformed = Program).

run_ir(Program, Goal, Answers) :-
    mnn_ir:ir_to_prolog(Program, Terms),
    setup_call_cleanup(
        temporary_source(Source),
        (write_terms(Source, Terms),
         mnn_sandbox_runner:run_program(Source, Goal, [], answers(Answers))),
        delete_file(Source)).

temporary_source(File) :-
    tmp_file_stream(text, File, Stream),
    close(Stream).

write_terms(_, []).
write_terms(File, [Term|Terms]) :-
    open(File, append, Stream),
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n'),
    close(Stream),
    write_terms(File, Terms).

:- end_tests(mnn_detlog_transform).

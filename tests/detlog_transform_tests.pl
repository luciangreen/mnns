:- begin_tests(mnn_detlog_transform).

:- use_module('../prolog/detlog/detlog_transform').

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
                                [mnn_clause(1, choose(CompiledValue),
                                            ite(disj(CompiledValue = a,
                                                     CompiledValue = b),
                                                true, fail),
                                            source(sample, 1))],
                                original)],
                      proof([]), trace([])),
    findall(SourceValue,
            once((SourceValue = a ; SourceValue = b)),
            OriginalAnswers),
    findall(CompiledAnswer,
            ((CompiledAnswer = a ; CompiledAnswer = b) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [a]),
    assertion(CompiledAnswers == OriginalAnswers).

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

:- end_tests(mnn_detlog_transform).

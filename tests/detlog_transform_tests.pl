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

test(compiles_builtin_member_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(choose/1, ['?'], [any],
                            [mnn_clause(1, choose(Value),
                                        once(member(Value, [a, b])),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(choose/1, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(choose/1, 1, member(_, [a, b]))])),
    assertion(Compiled = ite(Condition, true, fail)),
    Condition = member(CompiledValue, [a, b]),
    findall(OriginalValue,
            once(member(OriginalValue, [a, b])),
            OriginalAnswers),
    findall(CompiledValue,
            (call(Condition) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [a]),
    assertion(CompiledAnswers == OriginalAnswers).

test(compiles_builtin_between_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(choose/1, ['?'], [any],
                            [mnn_clause(1, choose(Value),
                                        once(between(1, 3, Value)),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(choose/1, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(choose/1, 1, between(1, 3, _))])),
    assertion(Compiled = ite(between(1, 3, CompiledValue), true, fail)),
    findall(OriginalValue,
            once(between(1, 3, OriginalValue)),
            OriginalAnswers),
    findall(CompiledValue,
            (between(1, 3, CompiledValue) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [1]),
    assertion(CompiledAnswers == OriginalAnswers).

test(keeps_once_for_program_defined_member) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2)]),
                  [mnn_pred(caller/2, ['?', '+'], [any, any],
                            [mnn_clause(1, caller(Value, List),
                                        once(member(Value, List)),
                                        source(sample, 1))],
                            original),
                   mnn_pred(member/2, ['?', '+'], [any, any],
                            [mnn_clause(2, member(Value, [Value|_]), true,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed,
        detlog_transform_report(
            [kept_once(caller/2, 1,
                       unsupported_goal(member(_, _)))])),
    assertion(Transformed = Program).

test(keeps_once_for_program_defined_between) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2)]),
                  [mnn_pred(caller/1, ['?'], [any],
                            [mnn_clause(1, caller(Value),
                                        once(between(1, 3, Value)),
                                        source(sample, 1))],
                            original),
                   mnn_pred(between/3, ['+', '+', '?'], [any, any, any],
                            [mnn_clause(2, between(_, _, _), true,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed,
        detlog_transform_report(
            [kept_once(caller/1, 1,
                       unsupported_goal(between(_, _, _)))])),
    assertion(Transformed = Program).

:- end_tests(mnn_detlog_transform).

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

test(compiles_builtin_append_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(split/2, ['?', '?'], [any, any],
                            [mnn_clause(1, split(Prefix, Suffix),
                                        once(append(Prefix, Suffix, [a, b])),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(split/2, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(split/2, 1, append(_, _, [a, b]))])),
    assertion(Compiled = ite(append(CompiledPrefix, CompiledSuffix, [a, b]),
                             true, fail)),
    findall(OriginalPrefix-OriginalSuffix,
            once(append(OriginalPrefix, OriginalSuffix, [a, b])),
            OriginalAnswers),
    findall(CompiledPrefix-CompiledSuffix,
            (append(CompiledPrefix, CompiledSuffix, [a, b]) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [[]-[a, b]]),
    assertion(CompiledAnswers == OriginalAnswers).

test(compiles_builtin_select_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(selected/2, ['?', '?'], [any, any],
                            [mnn_clause(1, selected(Value, Rest),
                                        once(select(Value, [a, a, b], Rest)),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(selected/2, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(selected/2, 1, select(_, [a, a, b], _))])),
    assertion(Compiled = ite(select(CompiledValue, [a, a, b], CompiledRest),
                             true, fail)),
    findall(OriginalValue-OriginalRest,
            once(select(OriginalValue, [a, a, b], OriginalRest)),
            OriginalAnswers),
    findall(CompiledValue-CompiledRest,
            (select(CompiledValue, [a, a, b], CompiledRest) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [a-[a, b]]),
    assertion(CompiledAnswers == OriginalAnswers).

test(compiles_builtin_append_and_select_failures) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2)]),
                  [mnn_pred(fails/0, [], [],
                            [mnn_clause(1, fails,
                                        once(append([a], [b], [c])),
                                        source(sample, 1)),
                             mnn_clause(2, fails,
                                        once(select(z, [a, b], _)),
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(fails/0, _, _,
                                    [mnn_clause(_, _, Append, _),
                                     mnn_clause(_, _, Select, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(fails/0, 1, append([a], [b], [c])),
             compiled_once(fails/0, 2, select(z, [a, b], _))])),
    assertion(Append = ite(append([a], [b], [c]), true, fail)),
    assertion(Select = ite(select(z, [a, b], _), true, fail)),
    assertion(\+ call(append([a], [b], [c]))),
    assertion(\+ call(select(z, [a, b], _))).

test(keeps_once_for_program_defined_append_and_select) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2),
                                        clause(3), clause(4)]),
                  [mnn_pred(caller/0, [], [],
                            [mnn_clause(1, caller,
                                        once(append(a, b, c)),
                                        source(sample, 1)),
                             mnn_clause(2, caller,
                                        once(select(a, b, c)),
                                        source(sample, 2))],
                            original),
                   mnn_pred(append/3, ['?', '?', '?'], [any, any, any],
                            [mnn_clause(3, append(_, _, _), true,
                                        source(sample, 3))],
                            original),
                   mnn_pred(select/3, ['?', '?', '?'], [any, any, any],
                            [mnn_clause(4, select(_, _, _), true,
                                        source(sample, 4))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed,
        detlog_transform_report(
            [kept_once(caller/0, 1, unsupported_goal(append(a, b, c))),
             kept_once(caller/0, 2, unsupported_goal(select(a, b, c)))])),
    assertion(Transformed = Program).

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

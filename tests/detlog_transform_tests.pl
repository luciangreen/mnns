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

test(compiles_builtin_length_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(first_length/2, ['?', '?'], [any, any],
                            [mnn_clause(1, first_length(List, Length),
                                        once(length(List, Length)),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(first_length/2, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(first_length/2, 1, length(_, _))])),
    assertion(Compiled = ite(length(CompiledList, CompiledLength),
                             true, fail)),
    findall(SourceList-SourceLength,
            once(length(SourceList, SourceLength)),
            OriginalAnswers),
    findall(CompiledList-CompiledLength,
            (length(CompiledList, CompiledLength) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [[]-0]),
    assertion(CompiledAnswers == OriginalAnswers).

test(compiles_builtin_nth0_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(first_nth0/2, ['?', '?'], [any, any],
                            [mnn_clause(1, first_nth0(Index, Value),
                                        once(nth0(Index, [a, b], Value)),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(first_nth0/2, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(first_nth0/2, 1, nth0(_, [a, b], _))])),
    assertion(Compiled = ite(nth0(CompiledIndex, [a, b], CompiledValue),
                             true, fail)),
    findall(SourceIndex-SourceValue,
            once(nth0(SourceIndex, [a, b], SourceValue)),
            OriginalAnswers),
    findall(CompiledIndex-CompiledValue,
            (nth0(CompiledIndex, [a, b], CompiledValue) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [0-a]),
    assertion(CompiledAnswers == OriginalAnswers).

test(compiles_builtin_nth1_once_and_preserves_first_answer, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(first_nth1/2, ['?', '?'], [any, any],
                            [mnn_clause(1, first_nth1(Index, Value),
                                        once(nth1(Index, [a, b], Value)),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(first_nth1/2, _, _,
                                    [mnn_clause(_, _, Compiled, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(first_nth1/2, 1, nth1(_, [a, b], _))])),
    assertion(Compiled = ite(nth1(CompiledIndex, [a, b], CompiledValue),
                             true, fail)),
    findall(SourceIndex-SourceValue,
            once(nth1(SourceIndex, [a, b], SourceValue)),
            OriginalAnswers),
    findall(CompiledIndex-CompiledValue,
            (nth1(CompiledIndex, [a, b], CompiledValue) -> true ; fail),
            CompiledAnswers),
    assertion(OriginalAnswers == [1-a]),
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

test(compiles_builtin_length_and_nth_failures) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2), clause(3)]),
                  [mnn_pred(fails/0, [], [],
                            [mnn_clause(1, fails,
                                        once(length([a, b], 1)),
                                        source(sample, 1)),
                             mnn_clause(2, fails,
                                        once(nth0(2, [a, b], _)),
                                        source(sample, 2)),
                             mnn_clause(3, fails,
                                        once(nth1(0, [a, b], _)),
                                        source(sample, 3))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(fails/0, _, _,
                                    [mnn_clause(_, _, Length, _),
                                     mnn_clause(_, _, Nth0, _),
                                     mnn_clause(_, _, Nth1, _)],
                                    original)], _, _),
        detlog_transform_report(
            [compiled_once(fails/0, 1, length([a, b], 1)),
             compiled_once(fails/0, 2, nth0(2, [a, b], _)),
             compiled_once(fails/0, 3, nth1(0, [a, b], _))])),
    assertion(Length = ite(length([a, b], 1), true, fail)),
    assertion(Nth0 = ite(nth0(2, [a, b], _), true, fail)),
    assertion(Nth1 = ite(nth1(0, [a, b], _), true, fail)),
    assertion(\+ call(length([a, b], 1))),
    assertion(\+ call(nth0(2, [a, b], _))),
    assertion(\+ call(nth1(0, [a, b], _))).

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

test(keeps_once_for_program_defined_length_and_nth) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2), clause(3),
                                        clause(4), clause(5), clause(6)]),
                  [mnn_pred(caller/0, [], [],
                            [mnn_clause(1, caller, once(length(a, b)),
                                        source(sample, 1)),
                             mnn_clause(2, caller, once(nth0(a, b, c)),
                                        source(sample, 2)),
                             mnn_clause(3, caller, once(nth1(a, b, c)),
                                        source(sample, 3))],
                            original),
                   mnn_pred(length/2, ['?', '?'], [any, any],
                            [mnn_clause(4, length(_, _), true,
                                        source(sample, 4))],
                            original),
                   mnn_pred(nth0/3, ['?', '?', '?'], [any, any, any],
                            [mnn_clause(5, nth0(_, _, _), true,
                                        source(sample, 5))],
                            original),
                   mnn_pred(nth1/3, ['?', '?', '?'], [any, any, any],
                            [mnn_clause(6, nth1(_, _, _), true,
                                        source(sample, 6))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed,
        detlog_transform_report(
            [kept_once(caller/0, 1, unsupported_goal(length(a, b))),
             kept_once(caller/0, 2, unsupported_goal(nth0(a, b, c))),
             kept_once(caller/0, 3, unsupported_goal(nth1(a, b, c)))])),
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

test(removes_redundant_green_cut_after_unification_in_single_clause,
     [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(choose/1, ['?'], [any],
                            [mnn_clause(1, choose(Value),
                                        conj(Value = a, !),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(choose/1, _, _,
                                    [mnn_clause(_, choose(CompiledValue),
                                                CompiledBody, _)],
                                    original)], _, _),
        detlog_transform_report([removed_green_cut(choose/1, 1)])),
    assertion(CompiledBody == (CompiledValue = a)),
    findall(OriginalValue,
            (OriginalValue = a, !),
            OriginalAnswers),
    findall(CompiledAnswer,
            (CompiledAnswer = a),
            CompiledAnswers),
    assertion(OriginalAnswers == [a]),
    assertion(CompiledAnswers == OriginalAnswers).

test(compiles_terminal_cut_after_nondeterministic_guard, [nondet]) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(choose/1, ['?'], [any],
                            [mnn_clause(1, choose(Value),
                                        conj(member(Value, [a, b]), !),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(choose/1, _, _,
                                   [mnn_clause(_, choose(CompiledValue),
                                               CompiledBody, _)],
                                   original)], _, _),
        detlog_transform_report(
            [compiled_cut(choose/1, 1, member(_, [a, b]))])),
    assertion(CompiledBody = ite(member(CompiledValue, [a, b]), true, fail)),
    findall(OriginalValue,
            (member(OriginalValue, [a, b]), !),
            OriginalAnswers),
    findall(TransformedValue,
            (member(TransformedValue, [a, b]) -> true ; fail),
            TransformedAnswers),
    assertion(OriginalAnswers == [a]),
    assertion(TransformedAnswers == OriginalAnswers).

test(keeps_cut_nested_in_terminal_guard) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(choose/1, ['?'], [any],
                           [mnn_clause(1, choose(Value),
                                       conj(conj(Value = a, !), !),
                                       source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed, detlog_transform_report([])),
    assertion(Transformed = Program).

test(keeps_cut_in_multi_clause_predicate) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2)]),
                  [mnn_pred(choose/1, ['?'], [any],
                            [mnn_clause(1, choose(Value),
                                        conj(Value = a, !),
                                        source(sample, 1)),
                             mnn_clause(2, choose(Value),
                                        Value = b,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program, Transformed, detlog_transform_report([])),
    assertion(Transformed = Program).

test(removes_cut_after_deterministic_builtin_guard) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1)]),
                  [mnn_pred(positive/1, ['?'], [any],
                            [mnn_clause(1, positive(Value),
                                        conj(conj(integer(Value),
                                                  Value > 0),
                                             !),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(positive/1, _, _,
                                    [mnn_clause(1, positive(CompiledValue),
                                                conj(integer(CompiledValue),
                                                     CompiledValue > 0),
                                                _)],
                                    original)], _, _),
        detlog_transform_report([removed_green_cut(positive/1, 1)])),
    findall(Input,
            ( member(Input, [a, -1, 0, 1, 2]),
              deterministic_guard_with_cut(Input)
            ),
            SourceAnswers),
    findall(Input,
            ( member(Input, [a, -1, 0, 1, 2]),
              deterministic_guard_without_cut(Input)
            ),
            TransformedAnswers),
    assertion(SourceAnswers == TransformedAnswers).

test(does_not_assume_shadowed_guard_is_deterministic) :-
    Program = mnn_program(
                  sample, meta(sample, [clause(1), clause(2)]),
                  [mnn_pred(positive/1, ['?'], [any],
                            [mnn_clause(1, positive(Value),
                                        conj(integer(Value), !),
                                        source(sample, 1))],
                            original),
                   mnn_pred(integer/1, ['?'], [any],
                            [mnn_clause(2, integer(_), true,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog_transform:transform_program(
        Program,
        mnn_program(_, _, [mnn_pred(positive/1, _, _,
                                    [mnn_clause(1, positive(CompiledValue),
                                                ite(integer(CompiledValue),
                                                    true, fail), _)],
                                    original),
                           _], _, _),
        detlog_transform_report(
            [compiled_cut(positive/1, 1, integer(_))])).

deterministic_guard_with_cut(Value) :-
    integer(Value),
    Value > 0,
    !.

deterministic_guard_without_cut(Value) :-
    integer(Value),
    Value > 0.

:- end_tests(mnn_detlog_transform).

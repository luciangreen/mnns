:- begin_tests(mnn_detlog).

:- use_module('../prolog/detlog/detlog').

test(classifies_supported_success_counts) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(always/1, ['?'], [any],
                            [mnn_clause(1, always(_X1), true,
                                        source(sample, 1))],
                            original),
                   mnn_pred(maybe/1, ['?'], [any],
                            [mnn_clause(2, maybe(a), true, source(sample, 2))],
                            original),
                   mnn_pred(never/1, ['?'], [any],
                            [mnn_clause(3, never(_X2), fail,
                                        source(sample, 3))],
                            original),
                   mnn_pred(multiple/1, ['?'], [any],
                            [mnn_clause(4, multiple(_X3),
                                        disj(true, true), source(sample, 4))],
                            original),
                   mnn_pred(choice/1, ['?'], [any],
                            [mnn_clause(5, choice(_X4),
                                        disj(fail, disj(true, true)),
                                        source(sample, 5))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(Program, detlog_report(Results)),
    assertion(memberchk(predicate(always/1, mode(all_arguments_unbound),
                                  determinism(det), success_counts([1])),
                        Results)),
    assertion(memberchk(predicate(maybe/1, mode(all_arguments_unbound),
                                  determinism(semidet), success_counts([0, 1])),
                        Results)),
    assertion(memberchk(predicate(never/1, mode(all_arguments_unbound),
                                  determinism(failure), success_counts([0])),
                        Results)),
    assertion(memberchk(predicate(multiple/1, mode(all_arguments_unbound),
                                  determinism(multi), success_counts([2])),
                        Results)),
    assertion(memberchk(predicate(choice/1, mode(all_arguments_unbound),
                                  determinism(multi), success_counts([2])),
                        Results)).

test(classifies_disjoint_clause_heads_as_semidet) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(colour/1, ['?'], [any],
                            [mnn_clause(1, colour(red), true,
                                        source(sample, 1)),
                             mnn_clause(2, colour(blue), true,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(
        Program,
        detlog_report(
            [predicate(colour/1, mode(all_arguments_unbound),
                       determinism(semidet), success_counts([0, 1]))])).

test(reports_unsupported_goals_without_guessing) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(committed/1, ['?'], [any],
                            [mnn_clause(1, committed(X), !, source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(
        Program,
        detlog_report(
            [predicate(committed/1, mode(all_arguments_unbound),
                       unavailable(unsupported_goal(!)), unsupported_body)])).

test(classifies_normalized_control_flow) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(conditional/1, ['?'], [any],
                            [mnn_clause(1, conditional(X),
                                        ite(integer(X), true, fail),
                                        source(sample, 1))],
                            original),
                   mnn_pred(negated/1, ['?'], [any],
                            [mnn_clause(2, negated(X), not(fail),
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(Program, detlog_report(Results)),
    assertion(memberchk(predicate(conditional/1, mode(all_arguments_unbound),
                                  determinism(semidet),
                                  success_counts([0, 1])), Results)),
    assertion(memberchk(predicate(negated/1, mode(all_arguments_unbound),
                                  determinism(det), success_counts([1])),
                        Results)).

test(once_caps_multiple_successes_at_one) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(single/0, [], [],
                           [mnn_clause(1, single, once(disj(true, true)),
                                       source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(
        Program,
        detlog_report(
            [predicate(single/0, mode(all_arguments_unbound),
                       determinism(det), success_counts([1]))])).

test(once_preserves_possible_failure) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(maybe_once/0, [], [],
                           [mnn_clause(1, maybe_once,
                                       once(disj(fail, disj(true, true))),
                                       source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(
        Program,
        detlog_report(
            [predicate(maybe_once/0, mode(all_arguments_unbound),
                       determinism(semidet), success_counts([0, 1]))])).

test(once_propagates_unsupported_inner_goals) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(committed_once/0, [], [],
                           [mnn_clause(1, committed_once, once(!),
                                       source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(
        Program,
        detlog_report(
            [predicate(committed_once/0, mode(all_arguments_unbound),
                       unavailable(unsupported_goal(!)), unsupported_body)])).

test(universal_head_with_overlapping_clause_is_multi) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(overlap/1, ['?'], [any],
                            [mnn_clause(1, overlap(_Any), true,
                                        source(sample, 1)),
                             mnn_clause(2, overlap(a), true,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(
        Program,
        detlog_report(
            [predicate(overlap/1, mode(all_arguments_unbound),
                       determinism(multi), success_counts([2]))])).

test(analyzes_acyclic_zero_arity_user_calls) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(always/0, [], [],
                           [mnn_clause(1, always, true,
                                       source(sample, 1))],
                           original),
                   mnn_pred(multiple/0, [], [],
                           [mnn_clause(2, multiple, disj(true, true),
                                       source(sample, 2))],
                           original),
                   mnn_pred(nested/0, [], [],
                           [mnn_clause(3, nested, always,
                                       source(sample, 3))],
                           original),
                   mnn_pred(caller/1, ['?'], [any],
                           [mnn_clause(4, caller(_X),
                                       conj(nested, multiple),
                                       source(sample, 4))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(Program, detlog_report(Results)),
    assertion(memberchk(predicate(nested/0, mode(all_arguments_unbound),
                                 determinism(det), success_counts([1])),
                       Results)),
    assertion(memberchk(predicate(caller/1, mode(all_arguments_unbound),
                                 determinism(multi), success_counts([2])),
                       Results)).

test(analyzes_acyclic_calls_with_distinct_unbound_arguments) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(always/1, ['?'], [any],
                           [mnn_clause(1, always(_Value), true,
                                       source(sample, 1))],
                           original),
                   mnn_pred(multiple/2, ['?', '?'], [any, any],
                           [mnn_clause(2, multiple(_Left, _Right),
                                       disj(true, true), source(sample, 2))],
                           original),
                   mnn_pred(nested/1, ['?'], [any],
                           [mnn_clause(3, nested(Value), always(Value),
                                       source(sample, 3))],
                           original),
                   mnn_pred(caller/2, ['?', '?'], [any, any],
                           [mnn_clause(4, caller(Left, Right),
                                       multiple(Left, Right),
                                       source(sample, 4))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(Program, detlog_report(Results)),
    assertion(memberchk(predicate(nested/1, mode(all_arguments_unbound),
                                determinism(det), success_counts([1])),
                       Results)),
    assertion(memberchk(predicate(caller/2, mode(all_arguments_unbound),
                                determinism(multi), success_counts([2])),
                       Results)).

test(reports_bound_and_repeated_argument_calls_as_unsupported) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(source/2, ['?', '?'], [any, any],
                           [mnn_clause(1, source(_Left, _Right), true,
                                       source(sample, 1))],
                           original),
                   mnn_pred(bound_caller/1, ['?'], [any],
                           [mnn_clause(2, bound_caller(Value),
                                       source(fixed, Value),
                                       source(sample, 2))],
                           original),
                   mnn_pred(repeated_caller/1, ['?'], [any],
                           [mnn_clause(3, repeated_caller(Value),
                                       source(Value, Value),
                                       source(sample, 3))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(Program, detlog_report(Results)),
    assertion(memberchk(predicate(bound_caller/1,
                                 mode(all_arguments_unbound),
                                 unavailable(unsupported_goal(source(fixed, _))),
                                 unsupported_body), Results)),
    assertion(memberchk(predicate(repeated_caller/1,
                                 mode(all_arguments_unbound),
                                 unavailable(unsupported_goal(source(_, _))),
                                 unsupported_body), Results)).

test(reports_recursive_user_calls_as_unavailable) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(loop/0, [], [],
                           [mnn_clause(1, loop, loop, source(sample, 1))],
                           original),
                   mnn_pred(loop_arg/1, ['?'], [any],
                           [mnn_clause(2, loop_arg(Value), loop_arg(Value),
                                       source(sample, 2))],
                           original),
                   mnn_pred(caller/1, ['?'], [any],
                           [mnn_clause(3, caller(_X), loop,
                                       source(sample, 3))],
                           original),
                   mnn_pred(argument_caller/1, ['?'], [any],
                           [mnn_clause(4, argument_caller(Value),
                                       loop_arg(Value),
                                       source(sample, 4))],
                           original)],
                  proof([]), trace([])),
    mnn_detlog:analyze_determinism(Program, detlog_report(Results)),
    assertion(memberchk(predicate(loop/0, mode(all_arguments_unbound),
                                 unavailable(recursive_call(loop/0)),
                                 unsupported_body), Results)),
    assertion(memberchk(predicate(caller/1, mode(all_arguments_unbound),
                                 unavailable(recursive_call(loop/0)),
                                 unsupported_body), Results)),
    assertion(memberchk(predicate(loop_arg/1, mode(all_arguments_unbound),
                                 unavailable(recursive_call(loop_arg/1)),
                                 unsupported_body), Results)),
    assertion(memberchk(predicate(argument_caller/1,
                                 mode(all_arguments_unbound),
                                 unavailable(recursive_call(loop_arg/1)),
                                 unsupported_body), Results)).

:- end_tests(mnn_detlog).

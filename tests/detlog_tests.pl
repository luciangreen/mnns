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
                                  determinism(nondet), success_counts([0, 2])),
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

:- end_tests(mnn_detlog).

:- begin_tests(mnn_pid).

:- use_module('../prolog/pid/pid').

test(classifies_direct_and_mutual_recursion) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(direct/1, ['?'], [any],
                            [mnn_clause(1, direct(X), direct(X), source(sample, 1))],
                            original),
                   mnn_pred(even/1, ['?'], [any],
                            [mnn_clause(2, even(N), odd(N), source(sample, 2))],
                            original),
                   mnn_pred(odd/1, ['?'], [any],
                            [mnn_clause(3, odd(N), even(N), source(sample, 3))],
                            original)],
                  proof([]), trace([])),
    mnn_pid:analyze_program(
        Program,
        pid_report([predicate(direct/1, recursive),
                    predicate(even/1, recursive),
                    predicate(odd/1, recursive)])).

test(classifies_non_recursive_wrapper) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(reverse/2, ['?', '?'], [any, any],
                            [mnn_clause(1, reverse(L, R),
                                        reverse_acc(L, [], R),
                                        source(sample, 1))],
                            original),
                   mnn_pred(reverse_acc/3, ['?', '?', '?'], [any, any, any],
                            [mnn_clause(2, reverse_acc([], Acc, Acc), true,
                                        source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_pid:analyze_program(
        Program,
        pid_report([predicate(reverse/2, non_recursive),
                    predicate(reverse_acc/3, non_recursive)])).

test(finds_structural_measure_for_direct_list_recursion) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(walk/1, ['?'], [any],
                           [mnn_clause(1, walk([]), true, source(sample, 1)),
                            mnn_clause(2, walk([_|Tail]), walk(Tail),
                                       source(sample, 2))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(walk/1,
                      measure(structural(1),
                              [decrease(2, walk(_), structural(1))]))])).

test(finds_measure_on_recursive_argument_two) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(skip/2, ['?', '?'], [any, any],
                           [mnn_clause(1, skip(_, []), true, source(sample, 1)),
                            mnn_clause(2, skip(X, [_|Tail]), skip(X, Tail),
                                       source(sample, 2))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(skip/2,
                      measure(structural(2),
                              [decrease(2, skip(_, _), structural(2))]))])).

test(rejects_recursive_call_that_does_not_use_list_tail) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(same/1, ['?'], [any],
                           [mnn_clause(1, same([Head|Tail]),
                                       same([Head|Tail]), source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(same/1,
                      unavailable(no_decreasing_structural_measure))])).

test(reports_mutual_recursion_as_unsupported) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(even/1, ['?'], [any],
                           [mnn_clause(1, even([_|Tail]), odd(Tail),
                                       source(sample, 1))],
                           original),
                   mnn_pred(odd/1, ['?'], [any],
                           [mnn_clause(2, odd([_|Tail]), even(Tail),
                                       source(sample, 2))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(even/1, unavailable(mutual_recursion)),
             predicate(odd/1, unavailable(mutual_recursion))])).

test(classifies_non_recursive_measure_target) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(identity/1, ['?'], [any],
                           [mnn_clause(1, identity(_), true, source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report([predicate(identity/1, non_recursive)])).

:- end_tests(mnn_pid).

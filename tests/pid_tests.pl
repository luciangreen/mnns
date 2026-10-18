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

:- end_tests(mnn_pid).

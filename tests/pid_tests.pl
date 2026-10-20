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

test(analyzes_recursion_inside_once) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(walk/1, ['?'], [any],
                            [mnn_clause(1, walk([]), true, source(sample, 1)),
                             mnn_clause(2, walk([_|Tail]), once(walk(Tail)),
                                       source(sample, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_pid:analyze_program(
        Program,
        pid_report([predicate(walk/1, recursive)])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(walk/1,
                       measure(structural(1),
                              [decrease(2, walk(_), structural(1))]))])),
    mnn_pid:analyze_induction(
        Program,
        pid_induction_report(
            [predicate(walk/1,
                       induction(structural(1),
                                [clause_obligation(1, walk([]), true, []),
                                 clause_obligation(
                                     2, walk([_|_]), once(walk(_)),
                                     [induction_hypothesis(
                                          walk(_), structural(1))])]))])),
    mnn_pid:analyze_tail_recursion(
        Program,
        pid_tail_recursion_report(
            [predicate(walk/1,
                       tail_recursion(non_tail_recursive(
                           [recursive_call(2, walk(_))])))])).

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

test(finds_measure_for_nested_compound_subterm) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(walk/1, ['?'], [any],
                          [mnn_clause(1, walk(tree(_, node(_, Child))),
                                      walk(Child), source(sample, 1))],
                          original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(walk/1,
                      measure(structural(1),
                              [decrease(1, walk(_), structural(1))]))])).

test(finds_guarded_natural_number_decrease) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(count/1, ['?'], [any],
                           [mnn_clause(1, count(0), true, source(sample, 1)),
                            mnn_clause(
                               2, count(N),
                               conj(integer(N),
                                    conj(>(N, 0),
                                         conj(is(Next, -(N, 1)),
                                              count(Next)))),
                               source(sample, 2))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(count/1,
                       measure(natural(1),
                              [decrease(2, count(_), natural(1))]))])).

test(finds_guarded_natural_decrease_by_multiple) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(count/1, ['?'], [any],
                           [mnn_clause(1, count(N),
                                      conj(integer(N),
                                           conj(>=(N, 2),
                                                conj(is(Next, -(N, 2)),
                                                     count(Next)))),
                                      source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(count/1,
                       measure(natural(1),
                              [decrease(1, count(_), natural(1))]))])).

test(rejects_unsafe_multiple_decrease_with_positive_guard) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(count/1, ['?'], [any],
                           [mnn_clause(1, count(N),
                                      conj(integer(N),
                                           conj(>(N, 0),
                                                conj(is(Next, -(N, 2)),
                                                     count(Next)))),
                                      source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(count/1,
                       unavailable(no_decreasing_structural_measure))])).

test(rejects_natural_decrease_without_integer_guard) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(count/1, ['?'], [any],
                           [mnn_clause(
                               1, count(N),
                               conj(>(N, 0),
                                    conj(is(Next, -(N, 1)), count(Next))),
                               source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(count/1,
                       unavailable(no_decreasing_structural_measure))])).

test(rejects_natural_decrease_with_guard_after_recursive_call) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(count/1, ['?'], [any],
                           [mnn_clause(
                               1, count(N),
                               conj(is(Next, -(N, 1)),
                                    conj(count(Next),
                                         conj(integer(N), >(N, 0)))),
                               source(sample, 1))],
                           original)],
                  proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(count/1,
                       unavailable(no_decreasing_structural_measure))])).

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

test(finds_structural_measure_across_mutual_recursion) :-
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
            [predicate(even/1,
                      measure(structural(1),
                              [decrease(1, odd(_), structural(1))])),
             predicate(odd/1,
                      measure(structural(1),
                              [decrease(2, even(_), structural(1))]))])).

test(finds_natural_measure_across_mutual_recursion) :-
    Program = mnn_program(
                 sample, meta(sample, []),
                [mnn_pred(even/1, ['?'], [any],
                         [mnn_clause(1, even(0), true, source(sample, 1)),
                          mnn_clause(
                              2, even(N),
                              conj(integer(N),
                                   conj(>(N, 0),
                                        conj(is(Next, -(N, 1)),
                                             odd(Next)))),
                              source(sample, 2))],
                         original),
                 mnn_pred(odd/1, ['?'], [any],
                         [mnn_clause(3, odd(0), true, source(sample, 3)),
                          mnn_clause(
                              4, odd(N),
                              conj(integer(N),
                                   conj(>(N, 0),
                                        conj(is(Next, -(N, 1)),
                                             even(Next)))),
                              source(sample, 4))],
                         original)],
                proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(even/1,
                      measure(natural(1),
                              [decrease(2, odd(_), natural(1))])),
             predicate(odd/1,
                      measure(natural(1),
                              [decrease(4, even(_), natural(1))]))])).

test(rejects_mutual_natural_measure_when_any_call_does_not_decrease) :-
    Program = mnn_program(
                sample, meta(sample, []),
                [mnn_pred(even/1, ['?'], [any],
                         [mnn_clause(
                              1, even(N),
                              conj(integer(N),
                                   conj(>(N, 0),
                                        conj(is(Next, -(N, 1)),
                                             odd(Next)))),
                              source(sample, 1))],
                         original),
                 mnn_pred(odd/1, ['?'], [any],
                         [mnn_clause(
                              2, odd(N),
                              conj(integer(N), conj(>(N, 0), even(N))),
                              source(sample, 2))],
                         original)],
                proof([]), trace([])),
    mnn_pid:analyze_measures(
        Program,
        pid_measure_report(
            [predicate(even/1, unavailable(mutual_recursion)),
             predicate(odd/1, unavailable(mutual_recursion))])).

test(rejects_mutual_recursion_when_any_call_does_not_decrease) :-
    Program = mnn_program(
                sample, meta(sample, []),
                 [mnn_pred(even/1, ['?'], [any],
                          [mnn_clause(1, even([_|Tail]), odd(Tail),
                                      source(sample, 1))],
                          original),
                  mnn_pred(odd/1, ['?'], [any],
                          [mnn_clause(2, odd(Value), even(Value),
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

test(generates_structural_induction_obligations) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(walk/1, ['?'], [any],
                          [mnn_clause(1, walk([]), true, source(sample, 1)),
                           mnn_clause(2, walk([_|Tail]), walk(Tail),
                                      source(sample, 2))],
                          original)],
                  proof([]), trace([])),
    mnn_pid:analyze_induction(
        Program,
        pid_induction_report(
            [predicate(walk/1,
                      induction(structural(1),
                                [clause_obligation(1, walk([]), true, []),
                                 clause_obligation(
                                     2, walk([_|Tail]), walk(Tail),
                                     [induction_hypothesis(
                                          walk(Tail), structural(1))])]))])).

test(generates_natural_induction_obligations) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(count/1, ['?'], [any],
                          [mnn_clause(1, count(0), true, source(sample, 1)),
                           mnn_clause(
                               2, count(N),
                               conj(integer(N),
                                    conj(>(N, 0),
                                         conj(is(Next, -(N, 1)),
                                              count(Next)))),
                               source(sample, 2))],
                          original)],
                  proof([]), trace([])),
    mnn_pid:analyze_induction(
        Program,
        pid_induction_report(
            [predicate(count/1,
                      induction(natural(1),
                                [clause_obligation(1, count(0), true, []),
                                 clause_obligation(
                                     2, count(N),
                                     conj(integer(N),
                                          conj(>(N, 0),
                                               conj(is(Next, -(N, 1)),
                                                    count(Next)))),
                                     [induction_hypothesis(
                                          count(Next), natural(1))])]))])).

test(generates_mutual_induction_hypotheses) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(even/1, ['?'], [any],
                          [mnn_clause(1, even(0), true, source(sample, 1)),
                           mnn_clause(2, even(N1),
                                      conj(integer(N1),
                                           conj(>(N1, 0),
                                                conj(is(Next1, -(N1, 1)),
                                                     odd(Next1)))),
                                      source(sample, 2))],
                          original),
                  mnn_pred(odd/1, ['?'], [any],
                          [mnn_clause(3, odd(0), true, source(sample, 3)),
                           mnn_clause(4, odd(N2),
                                      conj(integer(N2),
                                           conj(>(N2, 0),
                                                conj(is(Next2, -(N2, 1)),
                                                     even(Next2)))),
                                      source(sample, 4))],
                          original)],
                  proof([]), trace([])),
    mnn_pid:analyze_induction(
        Program,
        pid_induction_report(
            [predicate(even/1,
                      induction(natural(1),
                                [clause_obligation(1, even(0), true, []),
                                 clause_obligation(
                                     2, even(N1), _,
                                     [induction_hypothesis(
                                          odd(Next1), natural(1))])])),
             predicate(odd/1,
                      induction(natural(1),
                                [clause_obligation(3, odd(0), true, []),
                                 clause_obligation(
                                     4, odd(N2), _,
                                     [induction_hypothesis(
                                          even(Next2), natural(1))])]))])).

test(induction_report_preserves_unsupported_measure_status) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(grow/1, ['?'], [any],
                          [mnn_clause(1, grow(N), grow(N), source(sample, 1))],
                          original)],
                  proof([]), trace([])),
    mnn_pid:analyze_induction(
        Program,
        pid_induction_report(
            [predicate(grow/1,
                      unavailable(no_decreasing_structural_measure))])).

test(induction_report_marks_non_recursive_predicate) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(identity/1, ['?'], [any],
                          [mnn_clause(1, identity(Value), true,
                                      source(sample, 1))],
                          original)],
                  proof([]), trace([])),
    mnn_pid:analyze_induction(
        Program,
        pid_induction_report([predicate(identity/1, non_recursive)])).

test(classifies_direct_tail_recursion) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(drop/1, ['?'], [any],
                            [mnn_clause(1, drop([_|Tail]), drop(Tail),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_pid:analyze_tail_recursion(
        Program,
        pid_tail_recursion_report(
            [predicate(drop/1, tail_recursion(tail_recursive))])).

test(reports_recursive_call_before_later_goal_as_non_tail) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(loop/1, ['?'], [any],
                            [mnn_clause(1, loop([_|Tail]),
                                        conj(loop(Tail), true),
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_pid:analyze_tail_recursion(
        Program,
        pid_tail_recursion_report(
            [predicate(loop/1,
                       tail_recursion(non_tail_recursive(
                           [recursive_call(1, loop(_))])))])).

test(classifies_non_recursive_tail_recursion_target) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(identity/1, ['?'], [any],
                            [mnn_clause(1, identity(_), true,
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_pid:analyze_tail_recursion(
        Program,
        pid_tail_recursion_report(
            [predicate(identity/1, non_recursive)])).

:- end_tests(mnn_pid).

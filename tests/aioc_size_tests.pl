:- begin_tests(mnn_aioc_size).

:- use_module('../prolog/aioc/size').

test(measures_empty_program) :-
    Program = mnn_program(empty, meta(empty, []), [], proof([]), trace([])),
    mnn_aioc_size:measure_program_size(
        Program,
        program_size(clauses(0), goals(0), predicates(0), term_nodes(0),
                     weighted_total(0))).

test(counts_control_goals_and_term_nodes) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(
                       sample/1, ['?'], [any],
                       [mnn_clause(
                            1, sample(Value),
                            conj(integer(Value),
                                 once(member(Value, [a, b]))),
                            source(sample, 1))],
                       original)],
                  proof([]), trace([])),
    mnn_aioc_size:measure_program_size(
        Program,
        program_size(clauses(1), goals(4), predicates(1), term_nodes(10),
                     weighted_total(16))).

test(counts_negation_disjunction_and_conditionals) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(
                       sample/1, ['?'], [any],
                       [mnn_clause(
                            1, sample(Value),
                            ite(not(integer(Value)),
                                disj(true, fail),
                                once(member(Value, [a, b]))),
                            source(sample, 1))],
                       original)],
                  proof([]), trace([])),
    mnn_aioc_size:measure_program_size(
        Program,
        program_size(clauses(1), goals(8), predicates(1), term_nodes(14),
                     weighted_total(24))).

test(counts_each_clause_in_a_predicate) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(
                       pair/2, ['?', '?'], [any, any],
                       [mnn_clause(1, pair(a, _), true, source(sample, 1)),
                        mnn_clause(2, pair(b, _), fail, source(sample, 2))],
                       original)],
                  proof([]), trace([])),
    mnn_aioc_size:measure_program_size(
        Program,
        program_size(clauses(2), goals(2), predicates(1), term_nodes(6),
                     weighted_total(11))).

:- end_tests(mnn_aioc_size).

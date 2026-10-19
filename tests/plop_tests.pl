:- begin_tests(mnn_plop).

:- use_module('../prolog/plop/plop').
:- use_module('../prolog/proof/proof_checker').

test(optimizes_one_finite_findall_with_checked_proof) :-
    findall_program(Original),
    mnn_plop:optimize_program(
        Original, Optimized,
        plop_report([applied(findall_to_fold, [_])], Proof, accepted)),
    assertion(Optimized \=@= Original),
    mnn_proof_checker:check_proof(Optimized, Original, Proof, accepted),
    Optimized = mnn_program(_, _, Predicates, _, _),
    assertion(member(mnn_pred(mnn_loop2_1/2, _, _, _, generated(loop2)),
                     Predicates)).

test(single_predicate_entry_point_uses_shared_pipeline) :-
    findall_program(Original),
    mnn_plop:optimize_predicate(
        Original, values/1, Optimized,
        plop_report([applied(findall_to_fold, [_])], Proof, accepted)),
    mnn_proof_checker:check_proof(Optimized, Original, Proof, accepted).

test(single_predicate_entry_point_keeps_unselected_conversion) :-
    findall_program(Original),
    mnn_plop:optimize_predicate(
        Original, numbers/1, Optimized,
        plop_report([kept(requested_predicate_not_converted(numbers/1))],
                    Proof, unchanged)),
    assertion(Optimized =@= Original),
    mnn_proof_checker:check_proof(Optimized, Original, Proof, accepted).

test(keeps_program_with_multiple_supported_conversions) :-
    findall_program(Original0),
    Original0 = mnn_program(Name, Meta, Predicates, Proof0, Trace),
    Predicates = [Facts, Values],
    Values = mnn_pred(_, Modes, Domains, [_], Status),
    Clause2 = mnn_clause(4, values_again(Again),
                         findall(X, num(X), Again), source(test, 4)),
    Original = mnn_program(
                   Name, Meta,
                   [Facts,
                    Values,
                    mnn_pred(values_again/1, Modes, Domains,
                             [Clause2], Status)],
                   Proof0, Trace),
    mnn_plop:optimize_program(
        Original, Optimized,
        plop_report([kept(multiple_conversions(2))], _, unchanged)),
    assertion(Optimized =@= Original).

test(reports_unknown_single_predicate) :-
    findall_program(Program),
    mnn_plop:optimize_predicate(
        Program, missing/0, Optimized,
        plop_report([kept(unknown_predicate(missing/0))], Proof, unchanged)),
    assertion(Optimized =@= Program),
    mnn_proof_checker:check_proof(Optimized, Program, Proof, accepted).

test(unsupported_generator_is_kept_with_identity_proof) :-
    unsupported_program(Program),
    mnn_plop:optimize_program(
        Program, Optimized,
        plop_report([kept(no_supported_conversion)], Proof, unchanged)),
    assertion(Optimized =@= Program),
    mnn_proof_checker:check_proof(Optimized, Program, Proof, accepted).

findall_program(
    mnn_program(
        sample,
        meta(source, [clause(1), clause(2), clause(3)]),
        [mnn_pred(num/1, ['?'], [any],
                  [mnn_clause(1, num(1), true, source(test, 1)),
                   mnn_clause(2, num(2), true, source(test, 2))],
                  original),
         mnn_pred(values/1, ['?'], [any],
                  [mnn_clause(3, values(Values),
                              findall(X, num(X), Values), source(test, 3))],
                  original)],
        proof([]), trace([]))).

unsupported_program(
    mnn_program(
        sample,
        meta(source, [clause(1)]),
        [mnn_pred(values/1, ['?'], [any],
                  [mnn_clause(1, values(Values),
                              findall(X, arbitrary_generator(X), Values),
                              source(test, 1))],
                  original)],
        proof([]), trace([]))).

:- end_tests(mnn_plop).

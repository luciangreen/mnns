:- begin_tests(mnn_aioc_simplify).

:- use_module('../prolog/aioc/simplify').
:- use_module('../prolog/proof/proof_checker').

test(removes_redundant_true_conjuncts_with_sequential_checked_steps) :-
    sample_program(Original),
    mnn_aioc_simplify:simplify_program(
        Original, Simplified, Proof,
        simplification_report(
            changes(2), OriginalSize, SimplifiedSize,
            structural_effect(smaller))),
    Simplified = mnn_program(
                     sample, meta(source, [clause(1)]),
                     [mnn_pred(p/1, ['?'], [any],
                               [mnn_clause(1, p(X), q(X), source(test, 1))],
                               original)],
                     proof([]), trace([])),
    mnn_proof_checker:check_proof(Simplified, Original, Proof, accepted),
    OriginalSize = program_size(_, _, _, _,
                                weighted_total(OriginalTotal)),
    SimplifiedSize = program_size(_, _, _, _,
                                  weighted_total(SimplifiedTotal)),
    assertion(SimplifiedTotal < OriginalTotal).

test(retains_unchanged_program_with_identity_proof) :-
    unchanged_program(Program),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, Proof,
        simplification_report(
            changes(0), Size, Size, structural_effect(unchanged))),
    assertion(Simplified =@= Program),
    assertion(Proof = proof([proof_step(
                                 1, identity, [],
                                 equivalent(domain(all), modes(all)))])).

test(does_not_remove_true_when_source_defines_true_predicate) :-
    defined_true_program(Original),
    mnn_aioc_simplify:simplify_program(
        Original, Simplified, Proof,
        simplification_report(changes(0), _, _, structural_effect(unchanged))),
    assertion(Simplified =@= Original),
    mnn_proof_checker:check_proof(Simplified, Original, Proof, accepted).

test(rejects_unjustified_true_removal) :-
    sample_program(Original),
    BadCandidate = mnn_program(
                       sample, meta(source, [clause(1)]),
                       [mnn_pred(p/1, ['?'], [any],
                                 [mnn_clause(1, p(_), disj(q(_), true),
                                             source(test, 1))],
                                 original)],
                       proof([]), trace([])),
    Proof = proof([proof_step(
                       1, remove_true_conjunct, [],
                       equivalent(domain(any), modes(all)))]),
    mnn_proof_checker:check_proof(
        BadCandidate, Original, Proof,
        rejected(invalid_or_unsupported_proof)).

sample_program(
    mnn_program(
        sample, meta(source, [clause(1)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(
                       1, p(X), conj(true, conj(q(X), true)),
                       source(test, 1))],
                  original)],
        proof([]), trace([]))).

unchanged_program(
    mnn_program(
        sample, meta(source, [clause(1)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(1, p(X), true, source(test, 1))],
                  original)],
        proof([]), trace([]))).

defined_true_program(
    mnn_program(
        sample, meta(source, [clause(1), clause(2)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(1, p(X), conj(true, q(X)), source(test, 1))],
                  original),
         mnn_pred(true/0, [], [], [mnn_clause(2, true, fail, source(test, 2))],
                  original)],
        proof([]), trace([]))).

:- end_tests(mnn_aioc_simplify).

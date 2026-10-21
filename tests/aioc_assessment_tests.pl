:- begin_tests(mnn_aioc_assessment).

:- use_module('../prolog/aioc/assessment').
:- use_module('../prolog/aioc/size').
:- use_module('../prolog/plop/plop').

test(assesses_size_only_after_accepted_identity_proof) :-
    Program = mnn_program(empty, meta(empty, []), [], proof([]), trace([])),
    identity_proof(Proof),
    mnn_aioc_assessment:assess_candidate(
        Program, Program, Proof,
        assessment(
            accepted,
            size_comparison(
                program_size(clauses(0), goals(0), predicates(0), term_nodes(0),
                             weighted_total(0)),
                program_size(clauses(0), goals(0), predicates(0), term_nodes(0),
                             weighted_total(0)),
                weighted_delta(0),
                structural_effect(unchanged)))).

test(does_not_compare_candidate_with_rejected_proof) :-
    Candidate = mnn_program(candidate, meta(candidate, []), [], proof([]),
                            trace([])),
    Original = mnn_program(original, meta(original, []), [], proof([]),
                           trace([])),
    mnn_aioc_assessment:assess_candidate(
        Candidate, Original, proof([]),
        assessment(rejected(invalid_or_unsupported_proof), not_assessed)).

test(compares_sizes_for_proof_accepted_rewrite) :-
    findall_program(Original),
    mnn_plop:optimize_program(
        Original, Candidate, plop_report(_, Proof, accepted)),
    mnn_aioc_assessment:assess_candidate(
        Candidate, Original, Proof,
        assessment(accepted,
                   size_comparison(OriginalSize, CandidateSize,
                                   weighted_delta(Delta),
                                   structural_effect(Effect)))),
    mnn_aioc_size:measure_program_size(Original, OriginalSize),
    mnn_aioc_size:measure_program_size(Candidate, CandidateSize),
    OriginalSize = program_size(_, _, _, _, weighted_total(OriginalTotal)),
    CandidateSize = program_size(_, _, _, _, weighted_total(CandidateTotal)),
    Delta is CandidateTotal - OriginalTotal,
    expected_structural_effect(Delta, Effect).

test(selects_cost_size_pareto_frontier_and_reports_dominated_candidates) :-
    identity_proof(Proof),
    small_program(Small),
    medium_program(Medium),
    large_program(Large),
    Candidates = [
        candidate(fast_large, Large, Large, Proof, 1),
        candidate(middle, Medium, Medium, Proof, 5),
        candidate(slow_small, Small, Small, Proof, 10),
        candidate(worse_large, Large, Large, Proof, 6)
    ],
    mnn_aioc_assessment:assess_candidates(Candidates, Frontier, Results),
    assertion(Frontier == [fast_large, middle, slow_small]),
    assertion(memberchk(
                  candidate_result(
                      worse_large,
                      accepted(cost(6), structural_size(_),
                               structural_effect(unchanged),
                               frontier(dominated))),
                  Results)).

test(keeps_candidates_with_equal_cost_and_size) :-
    small_program(Program),
    identity_proof(Proof),
    Candidates = [
        candidate(first, Program, Program, Proof, 2),
        candidate(second, Program, Program, Proof, 2)
    ],
    mnn_aioc_assessment:assess_candidates(Candidates, Frontier, _),
    assertion(Frontier == [first, second]).

test(excludes_candidates_with_rejected_proofs) :-
    small_program(Program),
    identity_proof(Proof),
    Candidates = [
        candidate(accepted, Program, Program, Proof, 2),
        candidate(rejected, Program, Program, proof([]), 1)
    ],
    mnn_aioc_assessment:assess_candidates(Candidates, Frontier, Results),
    assertion(Frontier == [accepted]),
    assertion(memberchk(
                  candidate_result(
                      rejected,
                      rejected(rejected(invalid_or_unsupported_proof))),
                  Results)).

test(rejects_negative_candidate_cost, [throws(error(domain_error(nonnegative_cost, -1), _))]) :-
    mnn_aioc_assessment:assess_candidates(
        [candidate(invalid, not_a_program, not_a_program, proof([]), -1)],
        _, _).

test(rejects_duplicate_candidate_ids,
     [throws(error(domain_error(unique_candidate_ids, [duplicate, duplicate]), _))]) :-
    small_program(Program),
    identity_proof(Proof),
    mnn_aioc_assessment:assess_candidates(
        [candidate(duplicate, Program, Program, Proof, 1),
         candidate(duplicate, Program, Program, Proof, 2)],
        _, _).

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

small_program(mnn_program(small, meta(small, []), [], proof([]), trace([]))).

medium_program(
    mnn_program(medium, meta(medium, [clause(1)]),
                [mnn_pred(answer/1, ['?'], [any],
                [mnn_clause(1, answer(ok), true,
                            source(medium, 1))],
                original)],
                proof([]), trace([]))).

large_program(
    mnn_program(large, meta(large, [clause(1), clause(2)]),
                [mnn_pred(answer/1, ['?'], [any],
                [mnn_clause(1, answer(ok), true,
                            source(large, 1)),
                 mnn_clause(2, answer(other), true,
                            source(large, 2))],
                original)],
                proof([]), trace([]))).

expected_structural_effect(Delta, smaller) :-
    Delta < 0,
    !.
expected_structural_effect(Delta, larger) :-
    Delta > 0,
    !.
expected_structural_effect(_, unchanged).

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))])).

:- end_tests(mnn_aioc_assessment).

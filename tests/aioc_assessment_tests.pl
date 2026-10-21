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

test(ranks_only_checked_candidates_by_size_and_name) :-
    findall_program(Original),
    identity_proof(IdentityProof),
    once(mnn_plop:optimize_program(
        Original, Optimized, plop_report(_, OptimizedProof, accepted))),
    mnn_aioc_assessment:rank_candidates(
        Original,
        [candidate(zeta, Original, IdentityProof),
         candidate(alpha, Original, IdentityProof),
         candidate(optimized, Optimized, OptimizedProof),
         candidate(rejected, Optimized, proof([]))],
        candidate_ranking(Ranked, Rejected)),
    assertion(Ranked = [ranked_candidate(_, _, _),
                        ranked_candidate(_, _, _),
                        ranked_candidate(_, _, _)]),
    assertion(Rejected = [rejected_candidate(
                              rejected,
                              rejected(invalid_or_unsupported_proof))]),
    maplist(ranked_candidate_size, Ranked, Sizes),
    msort(Sizes, SortedSizes),
    assertion(Sizes == SortedSizes),
    findall(Name,
            member(ranked_candidate(Name, Original, _), Ranked),
            OriginalCandidateNames),
    assertion(OriginalCandidateNames == [alpha, zeta]).

ranked_candidate_size(
    ranked_candidate(_, _, size_comparison(
                               _, program_size(_, _, _, _,
                                               weighted_total(Size)),
                               _, _)),
    Size).

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

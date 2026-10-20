:- begin_tests(mnn_aioc_assessment).

:- use_module('../prolog/aioc/assessment').

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

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))]) ).

:- end_tests(mnn_aioc_assessment).

:- module(mnn_aioc_assessment,
          [ assess_candidate/4
          ]).

:- use_module('../proof/proof_checker').
:- use_module('size').

assess_candidate(Candidate, Original, Proof, Assessment) :-
    mnn_proof_checker:check_proof(Candidate, Original, Proof, ProofResult),
    (   ProofResult == accepted
    ->  compare_program_sizes(Candidate, Original, Comparison),
        Assessment = assessment(accepted, Comparison)
    ;   Assessment = assessment(ProofResult, not_assessed)
    ).

compare_program_sizes(Candidate, Original,
                      size_comparison(OriginalSize, CandidateSize,
                                      weighted_delta(Delta),
                                      structural_effect(Effect))) :-
    mnn_aioc_size:measure_program_size(Original, OriginalSize),
    mnn_aioc_size:measure_program_size(Candidate, CandidateSize),
    OriginalSize = program_size(_, _, _, _, weighted_total(OriginalTotal)),
    CandidateSize = program_size(_, _, _, _, weighted_total(CandidateTotal)),
    Delta is CandidateTotal - OriginalTotal,
    structural_effect(Delta, Effect).

structural_effect(Delta, smaller) :-
    Delta < 0,
    !.
structural_effect(Delta, larger) :-
    Delta > 0,
    !.
structural_effect(_, unchanged).

:- module(mnn_aioc_assessment,
          [ assess_candidate/4,
            rank_candidates/3
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module('../proof/proof_checker').
:- use_module('size').

rank_candidates(Original, Candidates,
               candidate_ranking(Ranked, Rejected)) :-
    must_be(list, Candidates),
    maplist(assess_rank_candidate(Original), Candidates, Results),
    partition(accepted_rank_candidate, Results, Accepted, Rejected),
    maplist(candidate_rank_key, Accepted, Keyed),
    keysort(Keyed, Sorted),
    pairs_values(Sorted, Ranked).

assess_rank_candidate(Original, candidate(Name, Candidate, Proof), Result) :-
    (   atom(Name)
    ->  assess_candidate(Candidate, Original, Proof, Assessment),
        rank_candidate_result(Name, Candidate, Assessment, Result)
    ;   throw(error(domain_error(candidate_name, Name), _))
    ).
assess_rank_candidate(_, Candidate, _) :-
    throw(error(domain_error(candidate, Candidate), _)).

rank_candidate_result(Name, Candidate,
                      assessment(accepted, Comparison),
                      ranked_candidate(Name, Candidate, Comparison)) :-
    !.
rank_candidate_result(Name, _, assessment(ProofResult, not_assessed),
                      rejected_candidate(Name, ProofResult)).

accepted_rank_candidate(ranked_candidate(_, _, _)).

candidate_rank_key(
    ranked_candidate(Name, Candidate, Comparison),
    key(WeightedTotal, Name)-ranked_candidate(Name, Candidate, Comparison)) :-
    Comparison = size_comparison(_, CandidateSize, _, _),
    CandidateSize = program_size(_, _, _, _, weighted_total(WeightedTotal)).

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

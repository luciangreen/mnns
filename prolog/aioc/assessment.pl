:- module(mnn_aioc_assessment,
          [ assess_candidate/4,
            assess_candidates/3
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
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

assess_candidates(Candidates, Frontier, Results) :-
    must_be(list, Candidates),
    maplist(validate_candidate, Candidates),
    candidate_ids(Candidates, Ids),
    sort(Ids, UniqueIds),
    (   same_length(Ids, UniqueIds)
    ->  true
    ;   throw(error(domain_error(unique_candidate_ids, Ids), _))
    ),
    maplist(assess_candidate_entry, Candidates, Assessed),
    include(is_frontier_candidate(Assessed), Assessed, FrontierCandidates),
    maplist(assessed_candidate_id, FrontierCandidates, Frontier),
    maplist(candidate_result(Frontier), Assessed, Results).

validate_candidate(Candidate) :-
    (   nonvar(Candidate),
        Candidate = candidate(Id, _, _, _, Cost)
    ->  must_be(ground, Id),
        validate_cost(Cost)
    ;   throw(error(type_error(aioc_candidate, Candidate), _))
    ).

validate_cost(Cost) :-
    must_be(number, Cost),
    (   float(Cost)
    ->  float_class(Cost, Class),
        (   memberchk(Class, [zero, subnormal, normal])
        ->  true
        ;   throw(error(domain_error(finite_nonnegative_cost, Cost), _))
        )
    ;   true
    ),
    (   Cost >= 0
    ->  true
    ;   throw(error(domain_error(nonnegative_cost, Cost), _))
    ).

candidate_ids([], []).
candidate_ids([candidate(Id, _, _, _, _)|Candidates], [Id|Ids]) :-
    candidate_ids(Candidates, Ids).

assess_candidate_entry(
    candidate(Id, Program, Original, Proof, Cost),
    assessed(Id, Program, Cost, Size, Effect)) :-
    assess_candidate(Program, Original, Proof,
                    assessment(accepted,
                               size_comparison(_, CandidateSize, _,
                                               structural_effect(Effect)))),
    CandidateSize = program_size(_, _, _, _, weighted_total(Size)),
    !.
assess_candidate_entry(candidate(Id, Program, Original, Proof, Cost),
                       rejected(Id, Program, Original, Proof, Cost, Result)) :-
    assess_candidate(Program, Original, Proof,
                     assessment(Result, not_assessed)).

is_frontier_candidate(Assessed, Candidate) :-
    Candidate = assessed(_, _, _, _, _),
    \+ ( member(Other, Assessed),
         dominates(Other, Candidate)
       ).

dominates(assessed(_, _, CostA, SizeA, _),
          assessed(_, _, CostB, SizeB, _)) :-
    CostA =< CostB,
    SizeA =< SizeB,
    (CostA < CostB ; SizeA < SizeB).

assessed_candidate_id(assessed(Id, _, _, _, _), Id).

candidate_result(Frontier, assessed(Id, _, Cost, Size, Effect),
                 candidate_result(
                     Id,
                     accepted(cost(Cost), structural_size(Size),
                              structural_effect(Effect), frontier(Status)))) :-
    (   memberchk(Id, Frontier)
    ->  Status = selected
    ;   Status = dominated
    ).
candidate_result(_, rejected(Id, _, _, _, _, Result),
                 candidate_result(Id, rejected(Result))).

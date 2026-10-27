:- module(mnn_aioc_cycle,
          [ run_cycle/5,
            run_cycles/6
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module('../aioc/allocate').
:- use_module('../aioc/size').
:- use_module('../proof/proof_checker').
:- use_module('../quantum/qi_search').

run_cycle(Program, SearchOptions, AllocationOptions, Best,
          cycle_report(SearchReport, AllocationReport)) :-
    mnn_qi_search:qi_search(Program, SearchOptions, Best, SearchReport),
    SearchReport = qi_report(_, _, CandidateSummaries, _, _, _, _, _),
    once(member(candidate(original, _, _, _, cost(OriginalSize)),
                CandidateSummaries)),
    maplist(allocation_candidate(OriginalSize), CandidateSummaries, Candidates),
    mnn_aioc_allocate:allocate_resources(Candidates, AllocationOptions,
                                         AllocationReport).

run_cycles(Program, SearchOptions, AllocationOptions, CycleLimit, Best,
           cycle_history(StopReason, Cycles, Proof)) :-
    must_be(integer, CycleLimit),
    (   CycleLimit > 0
    ->  true
    ;   throw(error(domain_error(positive_integer, CycleLimit), _))
    ),
    run_cycles(1, CycleLimit, Program, SearchOptions, AllocationOptions,
               Program, [], [], Best, StopReason, Cycles, Proof).

run_cycles(Index, CycleLimit, Current, SearchOptions, AllocationOptions,
           Original, ProofSteps0, Cycles0, Best, StopReason, Cycles, Proof) :-
    run_cycle(Current, SearchOptions, AllocationOptions, Candidate,
              cycle_report(SearchReport, AllocationReport)),
    selected_candidate(SearchReport, Candidate, Name, StepProof),
    program_cost(Current, CurrentCost),
    program_cost(Candidate, CandidateCost),
    Cycle = cycle(Index, selected(Name), cost(CurrentCost, CandidateCost),
                  SearchReport, AllocationReport),
    reverse([Cycle|Cycles0], OrderedCycles),
    (   CandidateCost < CurrentCost
    ->  StepProof = proof(StepSteps),
    append(ProofSteps0, StepSteps, ProofSteps),
    check_composed_proof(Candidate, Original, proof(ProofSteps)),
        (   Index < CycleLimit
        ->  NextIndex is Index + 1,
            run_cycles(NextIndex, CycleLimit, Candidate,
                       SearchOptions, AllocationOptions, Original,
                       ProofSteps, [Cycle|Cycles0], Best, StopReason,
                       Cycles, Proof)
        ;   Best = Candidate,
            StopReason = cycle_limit,
            Cycles = OrderedCycles,
            Proof = proof(ProofSteps)
        )
    ;   Best = Current,
        (   ProofSteps0 == []
        ->  identity_proof(Proof)
        ;   Proof = proof(ProofSteps0)
        ),
        check_composed_proof(Best, Original, Proof),
        StopReason = fixed_point,
        Cycles = OrderedCycles
    ).

selected_candidate(qi_report(_, _, CandidateSummaries, _, selected(Name),
                             _, _, _),
                   Candidate, Name, Proof) :-
    once(( member(candidate(Name, Found, Proof, _, _), CandidateSummaries),
           Found =@= Candidate
         )).

allocation_candidate(OriginalSize,
                     candidate(Name, _, _, amplitude(Amplitude), cost(Cost)),
                     candidate(Name, assessment(Improvement), cost(Cost),
                               amplitude(Amplitude))) :-
    Improvement is max(0, OriginalSize - Cost).

program_cost(Program, Cost) :-
    mnn_aioc_size:measure_program_size(
        Program, program_size(_, _, _, _, weighted_total(Cost))).

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))])).

check_composed_proof(Program, Original, Proof) :-
    mnn_proof_checker:check_proof(Program, Original, Proof, Result),
    (   Result == accepted
    ->  true
    ;   throw(error(domain_error(composed_proof, Result), _))
    ).

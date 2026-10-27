:- module(mnn_aioc_cycle,
          [ run_cycle/5
          ]).

:- use_module(library(lists)).
:- use_module('../aioc/allocate').
:- use_module('../aioc/size').
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

allocation_candidate(OriginalSize,
                     candidate(Name, _, _, amplitude(Amplitude), cost(Cost)),
                     candidate(Name, assessment(Improvement), cost(Cost),
                               amplitude(Amplitude))) :-
    Improvement is max(0, OriginalSize - Cost).

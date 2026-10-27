:- module(mnn_aioc_allocate,
          [ allocate_resources/3
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

allocate_resources(Candidates, Options,
                   allocation_report(Seed, Mode, BudgetReport, Allocations)) :-
    must_be(list, Candidates),
    must_be(list, Options),
    validate_candidates(Candidates),
    allocation_options(Options, Seed, Mode, Budgets),
    sort_candidates(Candidates, SortedCandidates),
    maplist(candidate_weight(Mode), SortedCandidates, WeightedCandidates),
    maplist(candidate_weight_value, WeightedCandidates, Weights),
    sum_list(Weights, TotalWeight),
    maplist(allocate_candidate_resources(Seed, SortedCandidates, TotalWeight,
                                         WeightedCandidates, Budgets),
            WeightedCandidates, Allocations),
    maplist(budget_report, Budgets, BudgetReport).

validate_candidates(Candidates) :-
    maplist(validate_candidate, Candidates),
    findall(Name, member(candidate(Name, _, _, _), Candidates), Names),
    sort(Names, UniqueNames),
    (   same_length(Names, UniqueNames)
    ->  true
    ;   throw(error(domain_error(unique_candidate_names, Names), _))
    ).

validate_candidate(candidate(Name, assessment(Score), cost(Cost),
                            amplitude(Amplitude))) :-
    !,
    must_be(atom, Name),
    nonnegative_integer(Score, assessment_score),
    nonnegative_integer(Cost, candidate_cost),
    nonnegative_integer(Amplitude, candidate_amplitude).
validate_candidate(Candidate) :-
    throw(error(domain_error(aioc_candidate, Candidate), _)).

nonnegative_integer(Value, Type) :-
    must_be(integer, Value),
    (   Value >= 0
    ->  true
    ;   throw(error(domain_error(not_less_than_zero, Type-Value), _))
    ).

allocation_options(Options, Seed, Mode, Budgets) :-
    findall(Value, member(seed(Value), Options), Seeds),
    findall(Value, member(quantum(Value), Options), Modes),
    findall(Resource-Amount,
            ( member(budget(Resource, Amount), Options),
              valid_resource(Resource)
            ),
            SuppliedBudgets),
    reject_unknown_options(Options),
    unique_option(Seeds, 0, seed, Seed),
    unique_option(Modes, off, quantum, Mode),
    must_be(integer, Seed),
    (   Seed >= 0
    ->  true
    ;   throw(error(domain_error(not_less_than_zero, seed-Seed), _))
    ),
    (   memberchk(Mode, [off, inspired])
    ->  true
    ;   throw(error(domain_error(quantum_mode, Mode), _))
    ),
    validate_budgets(SuppliedBudgets),
    resource_names(Resources),
    maplist(budget_value(SuppliedBudgets), Resources, Budgets),
    !.

valid_resource(time).
valid_resource(memory).
valid_resource(workers).
valid_resource(depth).
valid_resource(data).
valid_resource(effort).

reject_unknown_options([]).
reject_unknown_options([seed(_)|Options]) :-
    !,
    reject_unknown_options(Options).
reject_unknown_options([quantum(_)|Options]) :-
    !,
    reject_unknown_options(Options).
reject_unknown_options([budget(Resource, _)|Options]) :-
    valid_resource(Resource),
    !,
    reject_unknown_options(Options).
reject_unknown_options([Option|_]) :-
    throw(error(domain_error(aioc_allocation_option, Option), _)).

unique_option([], Default, _, Default).
unique_option([Value], _, _, Value) :-
    !.
unique_option(_, _, Name, _) :-
    throw(error(domain_error(unique_option, Name), _)).

validate_budgets(Budgets) :-
    maplist(validate_budget, Budgets),
    pairs_keys(Budgets, Resources),
    sort(Resources, UniqueResources),
    (   same_length(Resources, UniqueResources)
    ->  true
    ;   throw(error(domain_error(unique_resource_budgets, Resources), _))
    ).

validate_budget(Resource-Amount) :-
    must_be(integer, Amount),
    (   Amount >= 0
    ->  true
    ;   throw(error(domain_error(not_less_than_zero, Resource-Amount), _))
    ).

budget_value(Budgets, Resource, Resource-Amount) :-
    memberchk(Resource-Amount, Budgets),
    !.
budget_value(_, Resource, Resource-0).

budget_report(Resource-Amount, budget(Resource, Amount)).

sort_candidates(Candidates, Sorted) :-
    map_list_to_pairs(candidate_name, Candidates, Keyed),
    keysort(Keyed, SortedKeyed),
    pairs_values(SortedKeyed, Sorted).

candidate_name(candidate(Name, _, _, _), Name).

candidate_weight(Mode,
                 candidate(Name, assessment(Score), cost(Cost),
                           amplitude(Amplitude)),
                 weighted_candidate(Name, Score, Cost, Amplitude, Weight)) :-
    ModeFactor is (Amplitude + 1),
    (   Mode == inspired
    ->  Numerator is (Score + 1) * ModeFactor
    ;   Numerator is Score + 1
    ),
    Weight is max(1, Numerator // (Cost + 1)).

candidate_weight_value(weighted_candidate(_, _, _, _, Weight), Weight).

allocate_candidate_resources(Seed, Candidates, TotalWeight, AllWeighted,
                             Budgets, Candidate,
                             candidate_allocation(Name, assessment(Score),
                                                  cost(Cost),
                                                  amplitude(Amplitude),
                                                  weight(Weight),
                                                  allocation(ResourceShares),
                                                  reason(proportional_weighted_share))) :-
    Candidate = weighted_candidate(Name, Score, Cost, Amplitude, Weight),
    maplist(allocate_resource(Seed, Candidates, TotalWeight, AllWeighted,
                              Candidate),
            Budgets, ResourceShares).

allocate_resource(Seed, Candidates, TotalWeight, AllWeighted, Candidate,
                  Resource-Budget, Resource-Share) :-
    Candidate = weighted_candidate(Name, _, _, _, Weight),
    BaseShare is Budget*Weight // TotalWeight,
    findall(OtherName-OtherRemainder,
            ( member(weighted_candidate(OtherName, _, _, _, OtherWeight),
                     AllWeighted),
              OtherRemainder is Budget*OtherWeight mod TotalWeight
            ),
            Remainders),
    remainder_order(Seed, Candidates, Remainders, OrderedNames),
    sum_weighted_shares(Budget, TotalWeight, AllWeighted, BaseShares),
    RemainingUnits is Budget - BaseShares,
    (   first_n_member(Name, RemainingUnits, OrderedNames)
    ->  Share is BaseShare + 1
    ;   Share is BaseShare
    ).

sum_weighted_shares(Budget, TotalWeight, Weighted, Sum) :-
    maplist(base_share(Budget, TotalWeight), Weighted, Shares),
    sum_list(Shares, Sum).

base_share(Budget, TotalWeight,
           weighted_candidate(_, _, _, _, Weight), Share) :-
    Share is Budget*Weight // TotalWeight.

remainder_order(Seed, Candidates, Remainders, OrderedNames) :-
    length(Candidates, Count),
    Offset is Seed mod Count,
    rotated_candidate_names(Candidates, Offset, RotatedNames),
    maplist(remainder_key(RotatedNames), Remainders, Keyed),
    keysort(Keyed, Sorted),
    pairs_values(Sorted, OrderedNames).

remainder_key(Names, Name-Remainder,
              key(NegativeRemainder, TieRank)-Name) :-
    nth0(TieRank, Names, Name),
    !,
    NegativeRemainder is -Remainder.

rotated_candidate_names(Candidates, Offset, Names) :-
    maplist(candidate_name, Candidates, SortedNames),
    length(Prefix, Offset),
    append(Prefix, Suffix, SortedNames),
    append(Suffix, Prefix, Names).

first_n_member(_, Count, _) :-
    Count =< 0,
    !,
    fail.
first_n_member(Name, Count, Names) :-
    nth0(Index, Names, Name),
    Index < Count,
    !.

resource_names([time, memory, workers, depth, data, effort]).

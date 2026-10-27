:- begin_tests(mnn_aioc_allocate).

:- use_module('../prolog/aioc/allocate').

test(proportional_budget_uses_assessment_and_cost) :-
    Candidates = [candidate(alpha, assessment(2), cost(0), amplitude(0)),
                  candidate(beta, assessment(0), cost(0), amplitude(0))],
    mnn_aioc_allocate:allocate_resources(
        Candidates,
        [budget(time, 11), budget(workers, 3)],
        allocation_report(0, off, _, Allocations)),
    assertion(Allocations =
              [candidate_allocation(alpha, assessment(2), cost(0),
                                    amplitude(0), weight(3),
                                    allocation([time-8, memory-0, workers-2,
                                                depth-0, data-0, effort-0]), _),
               candidate_allocation(beta, assessment(0), cost(0),
                                    amplitude(0), weight(1),
                                    allocation([time-3, memory-0, workers-1,
                                                depth-0, data-0, effort-0]), _)]).

test(quantum_inspired_mode_uses_amplitudes) :-
    Candidates = [candidate(alpha, assessment(0), cost(0), amplitude(0)),
                  candidate(beta, assessment(0), cost(0), amplitude(3))],
    mnn_aioc_allocate:allocate_resources(
        Candidates,
        [quantum(inspired), budget(effort, 8)],
        allocation_report(0, inspired, _, Allocations)),
    assertion(Allocations =
              [candidate_allocation(alpha, _, _, _, weight(1),
                                    allocation([time-0, memory-0, workers-0,
                                                depth-0, data-0, effort-2]), _),
               candidate_allocation(beta, _, _, _, weight(4),
                                    allocation([time-0, memory-0, workers-0,
                                                depth-0, data-0, effort-6]), _)]).

test(seed_deterministically_breaks_equal_remainders) :-
    Candidates = [candidate(alpha, assessment(0), cost(0), amplitude(0)),
                  candidate(beta, assessment(0), cost(0), amplitude(0))],
    Options = [seed(0), budget(time, 1)],
    mnn_aioc_allocate:allocate_resources(
        Candidates, Options, First),
    mnn_aioc_allocate:allocate_resources(
        Candidates, Options, First),
    First = allocation_report(_, _, _, Allocations),
    assertion(Allocations =
              [candidate_allocation(alpha, _, _, _, _, allocation([time-1|_]),
                                    _),
               candidate_allocation(beta, _, _, _, _, allocation([time-0|_]),
                                    _)]).

test(seed_rotates_equal_remainder_assignment) :-
    Candidates = [candidate(alpha, assessment(0), cost(0), amplitude(0)),
                  candidate(beta, assessment(0), cost(0), amplitude(0))],
    mnn_aioc_allocate:allocate_resources(
        Candidates, [seed(1), budget(time, 1)],
        allocation_report(_, _, _, Allocations)),
    assertion(Allocations =
              [candidate_allocation(alpha, _, _, _, _, allocation([time-0|_]),
                                    _),
               candidate_allocation(beta, _, _, _, _, allocation([time-1|_]),
                                    _)]).

test(all_resource_budgets_are_hard_caps) :-
    Candidates = [candidate(alpha, assessment(2), cost(1), amplitude(2)),
                  candidate(beta, assessment(1), cost(4), amplitude(4)),
                  candidate(gamma, assessment(0), cost(0), amplitude(0))],
    Budgets = [budget(time, 7), budget(memory, 11), budget(workers, 3),
               budget(depth, 5), budget(data, 9), budget(effort, 13)],
    mnn_aioc_allocate:allocate_resources(
        Candidates, Budgets,
        allocation_report(_, _, _, Allocations)),
    forall(member(Resource-Budget,
                  [time-7, memory-11, workers-3, depth-5, data-9,
                   effort-13]),
           ( findall(Amount,
                     ( member(candidate_allocation(
                                  _, _, _, _, _, allocation(Shares), _),
                              Allocations),
                       memberchk(Resource-Amount, Shares)
                     ),
                     Amounts),
             sum_list(Amounts, Total),
             assertion(Total =:= Budget)
           )).

test(empty_candidate_set_leaves_budget_unallocated) :-
    mnn_aioc_allocate:allocate_resources(
        [], [budget(time, 5)],
        allocation_report(0, off, [budget(time, 5), _, _, _, _, _], [])).

test(rejects_duplicate_candidate_names,
     [throws(error(domain_error(unique_candidate_names, _), _))]) :-
    mnn_aioc_allocate:allocate_resources(
        [candidate(alpha, assessment(0), cost(0), amplitude(0)),
         candidate(alpha, assessment(1), cost(0), amplitude(0))],
        [], _).

test(rejects_negative_budgets,
     [throws(error(domain_error(not_less_than_zero, time- -1), _))]) :-
    mnn_aioc_allocate:allocate_resources([], [budget(time, -1)], _).

test(rejects_unknown_options,
     [throws(error(domain_error(aioc_allocation_option, unexplained(true)), _))]) :-
    mnn_aioc_allocate:allocate_resources([], [unexplained(true)], _).

:- end_tests(mnn_aioc_allocate).

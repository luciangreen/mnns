:- begin_tests(mnn_aioc_cycle).

:- use_module('../prolog/aioc/cycle').
:- use_module('../prolog/proof/proof_checker').

test(search_and_resource_plan_are_reproducible) :-
    findall_program(Program),
    SearchOptions = [seed(17), links([qi_link(values/1, num/1)])],
    AllocationOptions = [seed(17), quantum(inspired),
                         budget(time, 12), budget(workers, 3)],
    mnn_aioc_cycle:run_cycle(
        Program, SearchOptions, AllocationOptions, Best1, Report1),
    mnn_aioc_cycle:run_cycle(
        Program, SearchOptions, AllocationOptions, Best2, Report2),
    assertion(Best1 =@= Best2),
    assertion(Report1 =@= Report2),
    Report1 = cycle_report(qi_report(17, _, _, _, _, _, _, _),
                           allocation_report(17, inspired, _, Allocations)),
    forall(member(Resource-Budget, [time-12, workers-3]),
           allocation_total(Allocations, Resource, Budget)).

test(allocation_scores_only_reward_structural_reduction) :-
    findall_program(Program),
    mnn_aioc_cycle:run_cycle(
        Program, [], [budget(effort, 10)],
        _, cycle_report(qi_report(_, _, Candidates, _, _, _, _, _),
                        allocation_report(_, _, _, Allocations))),
    once(member(candidate(original, _, _, _, cost(OriginalSize)), Candidates)),
    forall(member(candidate(Name, _, _, _, cost(Cost)), Candidates),
           ( ExpectedScore is max(0, OriginalSize - Cost),
             once(member(candidate_allocation(
                             Name, assessment(ExpectedScore), cost(Cost), _, _,
                             allocation(_), _),
                         Allocations))
           )).

test(search_result_remains_proof_checked) :-
    findall_program(Program),
    mnn_aioc_cycle:run_cycle(
        Program, [], [], Best, cycle_report(qi_report(_, _, Candidates, _, _, _, _, _), _)),
    once(member(candidate(Name, Best, Proof, _, _), Candidates)),
    assertion(atom(Name)),
    once(mnn_proof_checker:check_proof(Best, Program, Proof, accepted)).

test(iterates_to_fixed_point_with_composed_proof) :-
    findall_program(Program),
    mnn_aioc_cycle:run_cycles(
        Program, [], [], 4, Best1, Report1),
    mnn_aioc_cycle:run_cycles(
        Program, [], [], 4, Best2, Report2),
    assertion(Best1 =@= Best2),
    assertion(Report1 =@= Report2),
    Report1 = cycle_history(fixed_point, Cycles, Proof),
    assertion(Cycles = [_|_]),
    assertion(mnn_proof_checker:check_proof(Best1, Program, Proof, accepted)).

test(fixed_point_takes_precedence_at_cycle_limit) :-
    findall_program(Program),
    mnn_aioc_cycle:run_cycles(
        Program, [], [], 1, Best,
        cycle_history(fixed_point, [cycle(1, _, _, _, _)], Proof)),
    assertion(mnn_proof_checker:check_proof(Best, Program, Proof, accepted)).

test(rejects_nonpositive_cycle_limit,
     [throws(error(domain_error(positive_integer, 0), _))]) :-
    findall_program(Program),
    mnn_aioc_cycle:run_cycles(Program, [], [], 0, _, _).

allocation_total(Allocations, Resource, Expected) :-
    findall(Amount,
            ( member(candidate_allocation(_, _, _, _, _, allocation(Shares), _),
                     Allocations),
              memberchk(Resource-Amount, Shares)
            ),
            Amounts),
    sum_list(Amounts, Total),
    assertion(Total =:= Expected).

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

:- end_tests(mnn_aioc_cycle).

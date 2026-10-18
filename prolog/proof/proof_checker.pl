:- module(mnn_proof_checker,
          [ check_proof/4
          ]).

check_proof(Program, Original, Proof, Result) :-
    (   mnn_program_term(Program),
        mnn_program_term(Original)
    ->  check_supported_proof(Program, Original, Proof, Result)
    ;   Result = rejected(invalid_program)
    ).

mnn_program_term(Program) :-
    nonvar(Program),
    functor(Program, mnn_program, 5).

check_supported_proof(Program, Original, Proof, Result) :-
    (   valid_identity_proof(Proof)
    ->  (   Program =@= Original
        ->  Result = accepted
        ;   Result = rejected(programs_differ)
        )
    ;   valid_goal_reordering_proof(Program, Original, Proof)
    ->  Result = accepted
    ;   Result = rejected(invalid_or_unsupported_proof)
    ).

valid_identity_proof(Proof) :-
    ground(Proof),
    Proof = proof([Step]),
    Step = proof_step(Id, Rule, Premises, Conclusion),
    integer(Id),
    Id > 0,
    Rule == identity,
    Premises == [],
    Conclusion = equivalent(domain(Domain), modes(Modes)),
    ground(Domain),
    ground(Modes).

valid_goal_reordering_proof(Program, Original, Proof) :-
    ground(Proof),
    Proof = proof([proof_step(Id, reorder_goals, [],
                              equivalent(domain(Domain), modes(Modes)))]),
    integer(Id),
    Id > 0,
    ground(Domain),
    ground(Modes),
    valid_reordering_program(Original),
    copy_term(Original, OriginalCopy),
    reorder_program(OriginalCopy, Reordered, 1),
    Program =@= Reordered.

valid_reordering_program(mnn_program(_, _, Predicates, _, _)) :-
    is_list(Predicates),
    maplist(valid_reordering_predicate, Predicates).

valid_reordering_predicate(Predicate) :-
    nonvar(Predicate),
    functor(Predicate, mnn_pred, 5),
    arg(4, Predicate, Clauses),
    is_list(Clauses),
    maplist(valid_reordering_clause, Clauses).

valid_reordering_clause(Clause) :-
    nonvar(Clause),
    functor(Clause, mnn_clause, 4).

reorder_program(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, ReorderedPredicates, Proof, Trace),
    Count) :-
    reorder_predicates(Predicates, ReorderedPredicates, Count).

reorder_predicates([], [], 0).
reorder_predicates([Predicate|Predicates], [Reordered|Rest], Count) :-
    reorder_predicate(Predicate, Reordered, PredicateCount),
    reorder_predicates(Predicates, Rest, RestCount),
    Count is PredicateCount + RestCount.

reorder_predicate(
    mnn_pred(Key, Modes, Domains, Clauses, Status),
    mnn_pred(Key, Modes, Domains, ReorderedClauses, Status),
    Count) :-
    reorder_clauses(Clauses, ReorderedClauses, Count).

reorder_clauses([], [], 0).
reorder_clauses(
    [mnn_clause(Id, Head, Body, Source)|Clauses],
    [mnn_clause(Id, Head, ReorderedBody, Source)|Rest],
    Count) :-
    reorder_goal(Body, ReorderedBody, ClauseCount),
    reorder_clauses(Clauses, Rest, RestCount),
    Count is ClauseCount + RestCount.

reorder_goal(conj(Left, Right), conj(Right, Left), 1) :-
    safe_ground_test(Left),
    safe_ground_test(Right),
    !.
reorder_goal(conj(Left, Right), conj(ReorderedLeft, Right), Count) :-
    reorder_goal(Left, ReorderedLeft, Count).
reorder_goal(conj(Left, Right), conj(Left, ReorderedRight), Count) :-
    reorder_goal(Right, ReorderedRight, Count).

safe_ground_test(Goal) :-
    ground(Goal),
    Goal =.. [Name, Argument],
    ground(Argument),
    memberchk(Name, [atom, atomic, compound, ground, integer, is_list, number]).

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
    ;   valid_definition_rewrite_proof(Program, Original, Proof)
    ->  Result = accepted
    ;   valid_proof_sequence(Program, Original, Proof)
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

valid_definition_rewrite_proof(Program, Original, Proof) :-
    ground(Proof),
    Proof = proof([proof_step(Id, Rule, [],
                              equivalent(domain(Domain), modes(Modes)))]),
    memberchk(Rule, [unfold, fold]),
    integer(Id),
    Id > 0,
    ground(Domain),
    ground(Modes),
    valid_rewrite_program(Original),
    copy_term(Original, OriginalCopy),
    rewrite_program(Rule, OriginalCopy, Rewritten),
    Program =@= Rewritten.

valid_proof_sequence(Program, Original, proof(Steps)) :-
    ground(Steps),
    is_list(Steps),
    Steps = [_,_|_],
    apply_proof_steps(Steps, Original, Rewritten),
    Program =@= Rewritten.

apply_proof_steps([], Program, Program).
apply_proof_steps([Step|Steps], Program0, Program) :-
    apply_proof_step(Step, Program0, Program1),
    apply_proof_steps(Steps, Program1, Program).

apply_proof_step(
    proof_step(Id, Rule, Premises,
               equivalent(domain(Domain), modes(Modes))),
    Program, Rewritten) :-
    integer(Id),
    Id > 0,
    Premises == [],
    ground(Domain),
    ground(Modes),
    apply_proof_rule(Rule, Program, Rewritten).

apply_proof_rule(identity, Program, Program).
apply_proof_rule(reorder_goals, Program, Rewritten) :-
    valid_reordering_program(Program),
    copy_term(Program, ProgramCopy),
    reorder_program(ProgramCopy, Rewritten, 1).
apply_proof_rule(Rule, Program, Rewritten) :-
    memberchk(Rule, [unfold, fold]),
    valid_rewrite_program(Program),
    copy_term(Program, ProgramCopy),
    rewrite_program(Rule, ProgramCopy, Rewritten).

valid_rewrite_program(mnn_program(_, _, Predicates, _, _)) :-
    is_list(Predicates),
    maplist(valid_rewrite_predicate, Predicates).

valid_rewrite_predicate(Predicate) :-
    nonvar(Predicate),
    functor(Predicate, mnn_pred, 5),
    arg(4, Predicate, Clauses),
    is_list(Clauses),
    maplist(valid_rewrite_clause, Clauses).

valid_rewrite_clause(Clause) :-
    nonvar(Clause),
    functor(Clause, mnn_clause, 4).

rewrite_program(Rule,
                mnn_program(Name, Meta, Predicates, Proof, Trace),
                mnn_program(Name, Meta, RewrittenPredicates, Proof, Trace)) :-
    rewrite_predicates(Rule, Predicates, Predicates,
                       RewrittenPredicates).

rewrite_predicates(Rule, Definitions, [Predicate|Predicates],
                   [Rewritten|Predicates]) :-
    rewrite_predicate(Rule, Definitions, Predicate, Rewritten).
rewrite_predicates(Rule, Definitions, [Predicate|Predicates],
                   [Predicate|RewrittenPredicates]) :-
    rewrite_predicates(Rule, Definitions, Predicates,
                       RewrittenPredicates).

rewrite_predicate(
    Rule, Definitions,
    mnn_pred(Key, Modes, Domains, Clauses, Status),
    mnn_pred(Key, Modes, Domains, RewrittenClauses, Status)) :-
    rewrite_clauses(Rule, Definitions, Key, Clauses, RewrittenClauses).

rewrite_clauses(Rule, Definitions, Key,
                [Clause|Clauses], [Rewritten|Clauses]) :-
    rewrite_clause(Rule, Definitions, Key, Clause, Rewritten).
rewrite_clauses(Rule, Definitions, Key,
                [Clause|Clauses], [Clause|RewrittenClauses]) :-
    rewrite_clauses(Rule, Definitions, Key, Clauses,
                    RewrittenClauses).

rewrite_clause(
    Rule, Definitions, Key,
    mnn_clause(Id, Head, Body, Source),
    mnn_clause(Id, Head, RewrittenBody, Source)) :-
    rewrite_goal(Rule, Definitions, Key, Body, RewrittenBody).

rewrite_goal(Rule, Definitions, Key, Goal, RewrittenGoal) :-
    nonvar(Goal),
    rewrite_nonvar_goal(Rule, Definitions, Key, Goal, RewrittenGoal).

rewrite_nonvar_goal(unfold, Definitions, _, Goal, Body) :-
    safe_definition(Definitions, _, Head, Body),
    Goal == Head.
rewrite_nonvar_goal(fold, Definitions, CallerKey, Goal, Head) :-
    safe_definition(Definitions, DefinitionKey, Head, Body),
    CallerKey \== DefinitionKey,
    Goal == Body.
rewrite_nonvar_goal(Rule, Definitions, Key, conj(Left, Right),
                    conj(RewrittenLeft, Right)) :-
    rewrite_goal(Rule, Definitions, Key, Left, RewrittenLeft).
rewrite_nonvar_goal(Rule, Definitions, Key, conj(Left, Right),
                    conj(Left, RewrittenRight)) :-
    rewrite_goal(Rule, Definitions, Key, Right, RewrittenRight).
rewrite_nonvar_goal(Rule, Definitions, Key, disj(Left, Right),
                    disj(RewrittenLeft, Right)) :-
    rewrite_goal(Rule, Definitions, Key, Left, RewrittenLeft).
rewrite_nonvar_goal(Rule, Definitions, Key, disj(Left, Right),
                    disj(Left, RewrittenRight)) :-
    rewrite_goal(Rule, Definitions, Key, Right, RewrittenRight).
rewrite_nonvar_goal(Rule, Definitions, Key, ite(If, Then, Else),
                    ite(RewrittenIf, Then, Else)) :-
    rewrite_goal(Rule, Definitions, Key, If, RewrittenIf).
rewrite_nonvar_goal(Rule, Definitions, Key, ite(If, Then, Else),
                    ite(If, RewrittenThen, Else)) :-
    rewrite_goal(Rule, Definitions, Key, Then, RewrittenThen).
rewrite_nonvar_goal(Rule, Definitions, Key, ite(If, Then, Else),
                    ite(If, Then, RewrittenElse)) :-
    rewrite_goal(Rule, Definitions, Key, Else, RewrittenElse).
rewrite_nonvar_goal(Rule, Definitions, Key, not(Goal),
                    not(RewrittenGoal)) :-
    rewrite_goal(Rule, Definitions, Key, Goal, RewrittenGoal).

safe_definition(Predicates, Key, Head, Body) :-
    member(mnn_pred(Key, _, _, [mnn_clause(_, Head, Body, _)], _),
           Predicates),
    ground(Head),
    ground(Body),
    functor(Head, Name, Arity),
    Key == Name/Arity,
    safe_pure_goal(Body),
    findall(Clauses,
            ( member(mnn_pred(OtherKey, _, _, Clauses, _), Predicates),
              OtherKey == Key
            ),
            [[mnn_clause(_, _, _, _)]]).

safe_pure_goal(true).
safe_pure_goal(fail).
safe_pure_goal(Goal) :-
    safe_ground_test(Goal).
safe_pure_goal(conj(Left, Right)) :-
    safe_pure_goal(Left),
    safe_pure_goal(Right).
safe_pure_goal(disj(Left, Right)) :-
    safe_pure_goal(Left),
    safe_pure_goal(Right).

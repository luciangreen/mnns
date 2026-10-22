:- module(mnn_aioc_simplify,
          [ simplify_program/4
          ]).

:- use_module('../proof/proof_checker').
:- use_module('size').

simplify_program(Program, Simplified, Proof,
                 simplification_report(changes(ChangeCount), OriginalSize,
                                       SimplifiedSize,
                                       structural_effect(Effect))) :-
    simplify_steps(Program, Simplified, 1, Steps),
    (   Steps == []
    ->  identity_proof(Proof)
    ;   Proof = proof(Steps)
    ),
    mnn_proof_checker:check_proof(Simplified, Program, Proof, accepted),
    mnn_aioc_size:measure_program_size(Program, OriginalSize),
    mnn_aioc_size:measure_program_size(Simplified, SimplifiedSize),
    length(Steps, ChangeCount),
    structural_effect(OriginalSize, SimplifiedSize, Effect).

simplify_steps(Program, Simplified, StepId, Steps) :-
    (   simplify_once(Program, Next, Rule)
    ->  Step = proof_step(StepId, Rule, [],
                         equivalent(domain(any), modes(all))),
        NextStepId is StepId + 1,
        Steps = [Step|Rest],
        simplify_steps(Next, Simplified, NextStepId, Rest)
    ;   Simplified = Program,
        Steps = []
    ).

simplify_once(Program, Next, remove_true_conjunct) :-
    remove_one_true_conjunct(Program, Next),
    !.
simplify_once(Program, Next, remove_fail_disjunct) :-
    remove_one_fail_disjunct(Program, Next).

remove_one_true_conjunct(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, SimplifiedPredicates, Proof, Trace)) :-
    is_list(Predicates),
    \+ defines_true_predicate(Predicates),
    simplify_predicates(Predicates, SimplifiedPredicates).

remove_one_fail_disjunct(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, SimplifiedPredicates, Proof, Trace)) :-
    is_list(Predicates),
    \+ defines_fail_predicate(Predicates),
    simplify_fail_predicates(Predicates, SimplifiedPredicates).

defines_true_predicate(Predicates) :-
    member(Predicate, Predicates),
    nonvar(Predicate),
    functor(Predicate, mnn_pred, 5),
    arg(1, Predicate, Key),
    Key == true/0.

defines_fail_predicate(Predicates) :-
    member(Predicate, Predicates),
    nonvar(Predicate),
    functor(Predicate, mnn_pred, 5),
    arg(1, Predicate, Key),
    Key == fail/0.

simplify_predicates([Predicate|Predicates],
                    [mnn_pred(Key, Modes, Domains, SimplifiedClauses, Status)
                     |Predicates]) :-
    nonvar(Predicate),
    Predicate = mnn_pred(Key, Modes, Domains, Clauses, Status),
    simplify_clauses(Clauses, SimplifiedClauses),
    !.
simplify_predicates([Predicate|Predicates],
                    [Predicate|SimplifiedPredicates]) :-
    simplify_predicates(Predicates, SimplifiedPredicates).

simplify_clauses([Clause|Clauses],
                 [mnn_clause(Id, Head, SimplifiedBody, Source)|Clauses]) :-
    nonvar(Clause),
    Clause = mnn_clause(Id, Head, Body, Source),
    simplify_goal(Body, SimplifiedBody),
    !.
simplify_clauses([Clause|Clauses], [Clause|SimplifiedClauses]) :-
    simplify_clauses(Clauses, SimplifiedClauses).

simplify_goal(Goal, Simplified) :-
    nonvar(Goal),
    simplify_nonvar_goal(Goal, Simplified).

simplify_nonvar_goal(conj(Left, Right), Right) :-
    Left == true,
    !.
simplify_nonvar_goal(conj(Left, Right), Left) :-
    Right == true,
    !.
simplify_nonvar_goal(conj(Left, Right), conj(SimplifiedLeft, Right)) :-
    simplify_goal(Left, SimplifiedLeft),
    !.
simplify_nonvar_goal(conj(Left, Right), conj(Left, SimplifiedRight)) :-
    simplify_goal(Right, SimplifiedRight),
    !.
simplify_nonvar_goal(disj(Left, Right), disj(SimplifiedLeft, Right)) :-
    simplify_goal(Left, SimplifiedLeft),
    !.
simplify_nonvar_goal(disj(Left, Right), disj(Left, SimplifiedRight)) :-
    simplify_goal(Right, SimplifiedRight),
    !.
simplify_nonvar_goal(ite(Condition, Then, Else),
                     ite(SimplifiedCondition, Then, Else)) :-
    simplify_goal(Condition, SimplifiedCondition),
    !.
simplify_nonvar_goal(ite(Condition, Then, Else),
                     ite(Condition, SimplifiedThen, Else)) :-
    simplify_goal(Then, SimplifiedThen),
    !.
simplify_nonvar_goal(ite(Condition, Then, Else),
                     ite(Condition, Then, SimplifiedElse)) :-
    simplify_goal(Else, SimplifiedElse),
    !.
simplify_nonvar_goal(not(Goal), not(SimplifiedGoal)) :-
    simplify_goal(Goal, SimplifiedGoal),
    !.
simplify_nonvar_goal(once(Goal), once(SimplifiedGoal)) :-
    simplify_goal(Goal, SimplifiedGoal).

simplify_fail_predicates(
    [Predicate|Predicates],
    [mnn_pred(Key, Modes, Domains, SimplifiedClauses, Status)|Predicates]) :-
    nonvar(Predicate),
    Predicate = mnn_pred(Key, Modes, Domains, Clauses, Status),
    simplify_fail_clauses(Clauses, SimplifiedClauses),
    !.
simplify_fail_predicates([Predicate|Predicates],
                         [Predicate|SimplifiedPredicates]) :-
    simplify_fail_predicates(Predicates, SimplifiedPredicates).

simplify_fail_clauses(
    [Clause|Clauses],
    [mnn_clause(Id, Head, SimplifiedBody, Source)|Clauses]) :-
    nonvar(Clause),
    Clause = mnn_clause(Id, Head, Body, Source),
    simplify_fail_goal(Body, SimplifiedBody),
    !.
simplify_fail_clauses([Clause|Clauses], [Clause|SimplifiedClauses]) :-
    simplify_fail_clauses(Clauses, SimplifiedClauses).

simplify_fail_goal(Goal, Simplified) :-
    nonvar(Goal),
    simplify_fail_nonvar_goal(Goal, Simplified).

simplify_fail_nonvar_goal(disj(Left, Right), Right) :-
    Left == fail,
    !.
simplify_fail_nonvar_goal(disj(Left, Right), Left) :-
    Right == fail,
    !.
simplify_fail_nonvar_goal(disj(Left, Right),
                          disj(SimplifiedLeft, Right)) :-
    simplify_fail_goal(Left, SimplifiedLeft),
    !.
simplify_fail_nonvar_goal(disj(Left, Right),
                          disj(Left, SimplifiedRight)) :-
    simplify_fail_goal(Right, SimplifiedRight),
    !.
simplify_fail_nonvar_goal(conj(Left, Right),
                          conj(SimplifiedLeft, Right)) :-
    simplify_fail_goal(Left, SimplifiedLeft),
    !.
simplify_fail_nonvar_goal(conj(Left, Right),
                          conj(Left, SimplifiedRight)) :-
    simplify_fail_goal(Right, SimplifiedRight),
    !.
simplify_fail_nonvar_goal(ite(Condition, Then, Else),
                          ite(SimplifiedCondition, Then, Else)) :-
    simplify_fail_goal(Condition, SimplifiedCondition),
    !.
simplify_fail_nonvar_goal(ite(Condition, Then, Else),
                          ite(Condition, SimplifiedThen, Else)) :-
    simplify_fail_goal(Then, SimplifiedThen),
    !.
simplify_fail_nonvar_goal(ite(Condition, Then, Else),
                          ite(Condition, Then, SimplifiedElse)) :-
    simplify_fail_goal(Else, SimplifiedElse),
    !.
simplify_fail_nonvar_goal(not(Goal), not(SimplifiedGoal)) :-
    simplify_fail_goal(Goal, SimplifiedGoal),
    !.
simplify_fail_nonvar_goal(once(Goal), once(SimplifiedGoal)) :-
    simplify_fail_goal(Goal, SimplifiedGoal).

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))])).

structural_effect(
    program_size(_, _, _, _, weighted_total(Original)),
    program_size(_, _, _, _, weighted_total(Simplified)),
    smaller) :-
    Simplified < Original,
    !.
structural_effect(_, _, unchanged).

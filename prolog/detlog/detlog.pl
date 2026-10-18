:- module(mnn_detlog,
          [ analyze_determinism/2
          ]).

:- use_module(library(lists)).

analyze_determinism(
    mnn_program(_, _, Predicates, _, _),
    detlog_report(Results)) :-
    maplist(analyze_predicate, Predicates, Results).

analyze_predicate(mnn_pred(Key, _, _, Clauses, _),
                  predicate(Key, mode(all_arguments_unbound),
                            Determinism, Evidence)) :-
    maplist(clause_outcomes, Clauses, ClauseOutcomes),
    (   member(clause_outcome(_, unavailable(Reason)), ClauseOutcomes)
    ->  Determinism = unavailable(Reason),
        Evidence = unsupported_body
    ;   predicate_outcomes(Clauses, ClauseOutcomes, Outcomes),
        outcomes_determinism(Outcomes, Class),
        Determinism = determinism(Class),
        Evidence = success_counts(Outcomes)
    ).

clause_outcomes(mnn_clause(_, Head, Body, _),
                clause_outcome(Head, Outcomes)) :-
    goal_outcomes(Body, Outcomes).

goal_outcomes(true, [1]) :-
    !.
goal_outcomes(fail, [0]) :-
    !.
goal_outcomes(conj(Left, Right), Outcomes) :-
    !,
    goal_outcomes(Left, LeftOutcomes),
    goal_outcomes(Right, RightOutcomes),
    (   LeftOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   RightOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   product_outcomes(LeftOutcomes, RightOutcomes, Outcomes)
    ).
goal_outcomes(disj(Left, Right), Outcomes) :-
    !,
    goal_outcomes(Left, LeftOutcomes),
    goal_outcomes(Right, RightOutcomes),
    (   LeftOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   RightOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   sum_outcomes(LeftOutcomes, RightOutcomes, Outcomes)
    ).
goal_outcomes(ite(Condition, Then, Else), Outcomes) :-
    !,
    goal_outcomes(Condition, ConditionOutcomes),
    goal_outcomes(Then, ThenOutcomes),
    goal_outcomes(Else, ElseOutcomes),
    (   ConditionOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   ThenOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   ElseOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   committed_outcomes(ConditionOutcomes, ThenOutcomes,
                           ElseOutcomes, Outcomes)
    ).
goal_outcomes(not(Goal), Outcomes) :-
    !,
    goal_outcomes(Goal, GoalOutcomes),
    (   GoalOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   negated_outcomes(GoalOutcomes, Outcomes)
    ).
goal_outcomes(Goal, [0, 1]) :-
    semidet_builtin(Goal),
    !.
goal_outcomes(Goal, unavailable(unsupported_goal(Goal))).

semidet_builtin(Goal) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    semidet_builtin_key(Name/Arity).

semidet_builtin_key((=)/2).
semidet_builtin_key((\=)/2).
semidet_builtin_key((==)/2).
semidet_builtin_key((\==)/2).
semidet_builtin_key(is/2).
semidet_builtin_key((>)/2).
semidet_builtin_key((>=)/2).
semidet_builtin_key((<)/2).
semidet_builtin_key((=<)/2).
semidet_builtin_key((=:=)/2).
semidet_builtin_key((=\=)/2).
semidet_builtin_key(var/1).
semidet_builtin_key(nonvar/1).
semidet_builtin_key(atom/1).
semidet_builtin_key(atomic/1).
semidet_builtin_key(compound/1).
semidet_builtin_key(ground/1).
semidet_builtin_key(integer/1).
semidet_builtin_key(number/1).
semidet_builtin_key(is_list/1).

predicate_outcomes([], _, [0]).
predicate_outcomes([_], [clause_outcome(Head, Outcomes)],
                   PredicateOutcomes) :-
    !,
    add_head_failure(Head, Outcomes, PredicateOutcomes).
predicate_outcomes(Clauses, ClauseOutcomes, Outcomes) :-
    clauses_pairwise_disjoint(Clauses),
    !,
    clause_success_counts(ClauseOutcomes, ClauseCounts),
    union_clause_outcomes(ClauseCounts, Union),
    add_zero(Union, Outcomes).
predicate_outcomes(_, ClauseOutcomes, Outcomes) :-
    clause_success_counts(ClauseOutcomes, ClauseCounts),
    sum_clause_outcomes(ClauseCounts, [0], Outcomes0),
    (   has_universal_clause(ClauseOutcomes)
    ->  Outcomes = Outcomes0
    ;   add_zero(Outcomes0, Outcomes)
    ).

clause_success_counts([], []).
clause_success_counts([clause_outcome(_, Outcomes)|Clauses], [Outcomes|Rest]) :-
    clause_success_counts(Clauses, Rest).

add_head_failure(Head, Outcomes, Outcomes) :-
    universal_head(Head),
    !.
add_head_failure(_, Outcomes, PredicateOutcomes) :-
    add_zero(Outcomes, PredicateOutcomes).

universal_head(Head) :-
    Head =.. [_|Arguments],
    distinct_variables(Arguments).

has_universal_clause(Clauses) :-
    member(clause_outcome(Head, _), Clauses),
    universal_head(Head),
    !.

distinct_variables([]).
distinct_variables([Variable|Variables]) :-
    var(Variable),
    \+ identical_member(Variable, Variables),
    distinct_variables(Variables).

identical_member(Variable, [Other|_]) :-
    Variable == Other,
    !.
identical_member(Variable, [_|Variables]) :-
    identical_member(Variable, Variables).

union_clause_outcomes([], []).
union_clause_outcomes([Outcomes|Rest], Union) :-
    union_clause_outcomes(Rest, RestUnion),
    append(Outcomes, RestUnion, All),
    sort(All, Union).

sum_clause_outcomes([], Outcomes, Outcomes).
sum_clause_outcomes([Next|Rest], Outcomes0, Outcomes) :-
    sum_outcomes(Outcomes0, Next, Outcomes1),
    sum_clause_outcomes(Rest, Outcomes1, Outcomes).

clauses_pairwise_disjoint([]).
clauses_pairwise_disjoint([mnn_clause(_, Head, _, _)|Clauses]) :-
    maplist(disjoint_from(Head), Clauses),
    clauses_pairwise_disjoint(Clauses).

disjoint_from(Head,
              mnn_clause(_, OtherHead, _, _)) :-
    copy_term(Head, HeadCopy),
    copy_term(OtherHead, OtherHeadCopy),
    \+ unify_with_occurs_check(HeadCopy, OtherHeadCopy).

add_zero(Outcomes0, Outcomes) :-
    append(Outcomes0, [0], All),
    sort(All, Outcomes).

product_outcomes(Left, Right, Outcomes) :-
    findall(Product,
            ( member(LeftCount, Left),
              member(RightCount, Right),
              multiply_count(LeftCount, RightCount, Product)
            ),
            Products),
    sort(Products, Outcomes).

multiply_count(0, _, 0) :-
    !.
multiply_count(_, 0, 0) :-
    !.
multiply_count(Left, Right, Product) :-
    Product is min(2, Left * Right).

sum_outcomes(Left, Right, Outcomes) :-
    findall(Sum,
            ( member(LeftCount, Left),
              member(RightCount, Right),
              Sum is min(2, LeftCount + RightCount)
            ),
            Sums),
    sort(Sums, Outcomes).

committed_outcomes(Condition, Then, Else, Outcomes) :-
    findall(Outcome,
            ( member(ConditionCount, Condition),
              (   ConditionCount =:= 0
              ->  member(Outcome, Else)
              ;   member(Outcome, Then)
              )
            ),
            Possible),
    sort(Possible, Outcomes).

negated_outcomes([0], [1]) :-
    !.
negated_outcomes(Outcomes, [0]) :-
    \+ memberchk(0, Outcomes),
    !.
negated_outcomes(_, [0, 1]).

outcomes_determinism([0], failure) :-
    !.
outcomes_determinism([1], det) :-
    !.
outcomes_determinism([0, 1], semidet) :-
    !.
outcomes_determinism([1, 2], multi) :-
    !.
outcomes_determinism([2], multi) :-
    !.
outcomes_determinism(_, nondet).

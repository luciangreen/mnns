:- module(mnn_aioc_size,
          [ measure_program_size/2
          ]).

:- use_module(library(lists)).

measure_program_size(
    mnn_program(_, _, Predicates, _, _),
    program_size(clauses(ClauseCount),
                 goals(GoalCount),
                 predicates(PredicateCount),
                 term_nodes(TermNodeCount),
                 weighted_total(WeightedTotal))) :-
    length(Predicates, PredicateCount),
    maplist(predicate_size, Predicates, Sizes),
    sum_size_field(Sizes, clauses, ClauseCount),
    sum_size_field(Sizes, goals, GoalCount),
    sum_size_field(Sizes, term_nodes, TermNodeCount),
    WeightedTotal is ClauseCount + GoalCount + PredicateCount + TermNodeCount.

predicate_size(mnn_pred(_, _, _, Clauses, _),
               size(clauses(ClauseCount),
                    goals(GoalCount),
                    term_nodes(TermNodeCount))) :-
    length(Clauses, ClauseCount),
    maplist(clause_size, Clauses, Sizes),
    sum_size_field(Sizes, goals, GoalCount),
    sum_size_field(Sizes, term_nodes, TermNodeCount).

clause_size(mnn_clause(_, Head, Body, _),
            size(goals(GoalCount), term_nodes(TermNodeCount))) :-
    goal_node_count(Body, GoalCount),
    term_node_count(Head, HeadTermNodes),
    term_node_count(Body, BodyTermNodes),
    TermNodeCount is HeadTermNodes + BodyTermNodes.

goal_node_count(Goal, Count) :-
    nonvar(Goal),
    Goal = conj(Left, Right),
    !,
    goal_node_count(Left, LeftCount),
    goal_node_count(Right, RightCount),
    Count is LeftCount + RightCount + 1.
goal_node_count(Goal, Count) :-
    nonvar(Goal),
    Goal = disj(Left, Right),
    !,
    goal_node_count(Left, LeftCount),
    goal_node_count(Right, RightCount),
    Count is LeftCount + RightCount + 1.
goal_node_count(Goal, Count) :-
    nonvar(Goal),
    Goal = ite(Condition, Then, Else),
    !,
    goal_node_count(Condition, ConditionCount),
    goal_node_count(Then, ThenCount),
    goal_node_count(Else, ElseCount),
    Count is ConditionCount + ThenCount + ElseCount + 1.
goal_node_count(Goal, Count) :-
    nonvar(Goal),
    Goal = not(InnerGoal),
    !,
    goal_node_count(InnerGoal, InnerCount),
    Count is InnerCount + 1.
goal_node_count(Goal, Count) :-
    nonvar(Goal),
    Goal = once(InnerGoal),
    !,
    goal_node_count(InnerGoal, InnerCount),
    Count is InnerCount + 1.
goal_node_count(_, 1).

term_node_count(Term, 0) :-
    var(Term),
    !.
term_node_count(Term, 1) :-
    atomic(Term),
    !.
term_node_count(Term, Count) :-
    compound(Term),
    Term =.. [_|Arguments],
    maplist(term_node_count, Arguments, Counts),
    sum_list(Counts, ChildCount),
    Count is ChildCount + 1.

sum_size_field([], _, 0).
sum_size_field([size(clauses(Count), _, _)|Sizes], clauses, Total) :-
    !,
    sum_size_field(Sizes, clauses, Rest),
    Total is Count + Rest.
sum_size_field([size(_, goals(Count), _)|Sizes], goals, Total) :-
    !,
    sum_size_field(Sizes, goals, Rest),
    Total is Count + Rest.
sum_size_field([size(_, _, term_nodes(Count))|Sizes], term_nodes, Total) :-
    !,
    sum_size_field(Sizes, term_nodes, Rest),
    Total is Count + Rest.
sum_size_field([size(goals(Count), term_nodes(_))|Sizes], goals, Total) :-
    !,
    sum_size_field(Sizes, goals, Rest),
    Total is Count + Rest.
sum_size_field([size(goals(_), term_nodes(Count))|Sizes], term_nodes, Total) :-
    !,
    sum_size_field(Sizes, term_nodes, Rest),
    Total is Count + Rest.

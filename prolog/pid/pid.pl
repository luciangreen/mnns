:- module(mnn_pid,
          [ analyze_program/2
          ]).

:- use_module(library(lists)).

analyze_program(mnn_program(_, _, Predicates, _, _), pid_report(Results)) :-
    predicate_keys(Predicates, Keys),
    call_edges(Predicates, Keys, Edges),
    maplist(classify_predicate(Edges), Keys, Results).

predicate_keys([], []).
predicate_keys([mnn_pred(Key, _, _, _, _)|Predicates], [Key|Keys]) :-
    predicate_keys(Predicates, Keys).

call_edges([], _, []).
call_edges([mnn_pred(Key, _, _, Clauses, _)|Predicates], Keys, Edges) :-
    clause_call_edges(Clauses, Key, Keys, ClauseEdges),
    call_edges(Predicates, Keys, OtherEdges),
    append(ClauseEdges, OtherEdges, Edges).

clause_call_edges([], _, _, []).
clause_call_edges([mnn_clause(_, _, Body, _)|Clauses], Key, Keys, Edges) :-
    goal_call_edges(Body, Key, Keys, BodyEdges),
    clause_call_edges(Clauses, Key, Keys, OtherEdges),
    append(BodyEdges, OtherEdges, Edges).

goal_call_edges(conj(Left, Right), Key, Keys, Edges) :-
    !,
    goal_call_edges(Left, Key, Keys, LeftEdges),
    goal_call_edges(Right, Key, Keys, RightEdges),
    append(LeftEdges, RightEdges, Edges).
goal_call_edges(disj(Left, Right), Key, Keys, Edges) :-
    !,
    goal_call_edges(Left, Key, Keys, LeftEdges),
    goal_call_edges(Right, Key, Keys, RightEdges),
    append(LeftEdges, RightEdges, Edges).
goal_call_edges(ite(If, Then, Else), Key, Keys, Edges) :-
    !,
    goal_call_edges(If, Key, Keys, IfEdges),
    goal_call_edges(Then, Key, Keys, ThenEdges),
    goal_call_edges(Else, Key, Keys, ElseEdges),
    append([IfEdges, ThenEdges, ElseEdges], Edges).
goal_call_edges(not(Goal), Key, Keys, Edges) :-
    !,
    goal_call_edges(Goal, Key, Keys, Edges).
goal_call_edges(Goal, Key, Keys, [edge(Key, CalledKey)]) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    CalledKey = Name/Arity,
    memberchk(CalledKey, Keys),
    !.
goal_call_edges(_, _, _, []).

classify_predicate(Edges, Key, predicate(Key, Status)) :-
    (   recursive_path(Key, Key, Edges)
    ->  Status = recursive
    ;   Status = non_recursive
    ).

recursive_path(Start, Target, Edges) :-
    memberchk(edge(Start, Next), Edges),
    path_to(Next, Target, Edges, [Start, Next]).

path_to(Current, Target, Edges, _) :-
    memberchk(edge(Current, Target), Edges).
path_to(Current, Target, Edges, Visited) :-
    memberchk(edge(Current, Next), Edges),
    \+ memberchk(Next, Visited),
    path_to(Next, Target, Edges, [Next|Visited]).

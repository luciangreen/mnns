:- module(mnn_pid,
          [ analyze_program/2,
            analyze_measures/2
          ]).

:- use_module(library(lists)).

analyze_program(mnn_program(_, _, Predicates, _, _), pid_report(Results)) :-
    predicate_keys(Predicates, Keys),
    call_edges(Predicates, Keys, Edges),
    maplist(classify_predicate(Edges), Keys, Results).

analyze_measures(
    mnn_program(_, _, Predicates, _, _),
    pid_measure_report(Results)) :-
    predicate_keys(Predicates, Keys),
    call_edges(Predicates, Keys, Edges),
    maplist(analyze_predicate_measure(Predicates, Edges), Keys, Results).

analyze_predicate_measure(_, Edges, Key, predicate(Key, non_recursive)) :-
    \+ recursive_path(Key, Key, Edges),
    !.
analyze_predicate_measure(_, Edges, Key,
                          predicate(Key, unavailable(mutual_recursion))) :-
    memberchk(edge(Key, Other), Edges),
    Other \== Key,
    path_to(Other, Key, Edges, [Key, Other]),
    !.
analyze_predicate_measure(Predicates, _, Key,
                          predicate(Key, measure(structural(Argument),
                                                 Obligations))) :-
    recursive_calls(Predicates, Key, Calls),
    Calls = [_|_],
    Key = _/Arity,
    between(1, Arity, Argument),
    maplist(decreases_structurally(Argument), Calls, Obligations),
    !.
analyze_predicate_measure(_, _, Key,
                          predicate(Key,
                                    unavailable(no_decreasing_structural_measure))).

recursive_calls(Predicates, Key, Calls) :-
    member(mnn_pred(DeclaredKey, _, _, Clauses, _), Predicates),
    DeclaredKey == Key,
    recursive_calls_in_clauses(Clauses, Key, Calls),
    !.

recursive_calls_in_clauses([], _, []).
recursive_calls_in_clauses(
    [mnn_clause(Id, Head, Body, _)|Clauses], Key, Calls) :-
    goal_recursive_calls(Body, Key, ClauseCalls),
    maplist(add_recursive_site(Id, Head), ClauseCalls, IdentifiedCalls),
    recursive_calls_in_clauses(Clauses, Key, OtherCalls),
    append(IdentifiedCalls, OtherCalls, Calls).

add_recursive_site(Id, Head, Call, recursive_site(Id, Head, Call)).

goal_recursive_calls(conj(Left, Right), Key, Calls) :-
    !,
    goal_recursive_calls(Left, Key, LeftCalls),
    goal_recursive_calls(Right, Key, RightCalls),
    append(LeftCalls, RightCalls, Calls).
goal_recursive_calls(disj(Left, Right), Key, Calls) :-
    !,
    goal_recursive_calls(Left, Key, LeftCalls),
    goal_recursive_calls(Right, Key, RightCalls),
    append(LeftCalls, RightCalls, Calls).
goal_recursive_calls(ite(If, Then, Else), Key, Calls) :-
    !,
    goal_recursive_calls(If, Key, IfCalls),
    goal_recursive_calls(Then, Key, ThenCalls),
    goal_recursive_calls(Else, Key, ElseCalls),
    append([IfCalls, ThenCalls, ElseCalls], Calls).
goal_recursive_calls(not(Goal), Key, Calls) :-
    !,
    goal_recursive_calls(Goal, Key, Calls).
goal_recursive_calls(Goal, Key, [Goal]) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    CalledKey = Name/Arity,
    CalledKey == Key,
    !.
goal_recursive_calls(_, _, []).

decreases_structurally(
    Argument, recursive_site(Id, Head, Call),
    decrease(Id, Call, structural(Argument))) :-
    arg(Argument, Head, HeadArgument),
    nonvar(HeadArgument),
    functor(HeadArgument, '[|]', 2),
    arg(2, HeadArgument, Tail),
    arg(Argument, Call, CallArgument),
    CallArgument == Tail.

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

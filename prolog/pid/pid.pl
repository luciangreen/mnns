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
analyze_predicate_measure(Predicates, Edges, Key,
                          predicate(Key, measure(structural(Argument),
                                                 Obligations))) :-
    mutually_recursive_component(Key, Edges, Keys),
    component_structural_measure(Predicates, Keys, Argument),
    recursive_calls(Predicates, Key, Keys, Calls),
    maplist(decreases_structurally(Argument), Calls, Obligations),
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
analyze_predicate_measure(Predicates, _, Key,
                          predicate(Key, measure(natural(Argument),
                                                 Obligations))) :-
    recursive_calls(Predicates, Key, Calls),
    Calls = [_|_],
    Key = _/Arity,
    between(1, Arity, Argument),
    maplist(decreases_naturally(Argument), Calls, Obligations),
    !.
analyze_predicate_measure(_, _, Key,
                          predicate(Key,
                                    unavailable(no_decreasing_structural_measure))).

recursive_calls(Predicates, Key, Calls) :-
    recursive_calls(Predicates, Key, [Key], Calls).

recursive_calls(Predicates, Key, Keys, Calls) :-
    member(mnn_pred(DeclaredKey, _, _, Clauses, _), Predicates),
    DeclaredKey == Key,
    recursive_calls_in_clauses(Clauses, Keys, Calls),
    !.

recursive_calls_in_clauses([], _, []).
recursive_calls_in_clauses(
    [mnn_clause(Id, Head, Body, _)|Clauses], Keys, Calls) :-
    goal_recursive_calls(Body, Keys, ClauseCalls),
    maplist(add_recursive_site(Id, Head, Body), ClauseCalls, IdentifiedCalls),
    recursive_calls_in_clauses(Clauses, Keys, OtherCalls),
    append(IdentifiedCalls, OtherCalls, Calls).

add_recursive_site(Id, Head, Body, Call,
                   recursive_site(Id, Head, Body, Call)).

goal_recursive_calls(conj(Left, Right), Keys, Calls) :-
    !,
    goal_recursive_calls(Left, Keys, LeftCalls),
    goal_recursive_calls(Right, Keys, RightCalls),
    append(LeftCalls, RightCalls, Calls).
goal_recursive_calls(disj(Left, Right), Keys, Calls) :-
    !,
    goal_recursive_calls(Left, Keys, LeftCalls),
    goal_recursive_calls(Right, Keys, RightCalls),
    append(LeftCalls, RightCalls, Calls).
goal_recursive_calls(ite(If, Then, Else), Keys, Calls) :-
    !,
    goal_recursive_calls(If, Keys, IfCalls),
    goal_recursive_calls(Then, Keys, ThenCalls),
    goal_recursive_calls(Else, Keys, ElseCalls),
    append([IfCalls, ThenCalls, ElseCalls], Calls).
goal_recursive_calls(not(Goal), Keys, Calls) :-
    !,
    goal_recursive_calls(Goal, Keys, Calls).
goal_recursive_calls(Goal, Keys, [Goal]) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    CalledKey = Name/Arity,
    memberchk(CalledKey, Keys),
    !.
goal_recursive_calls(_, _, []).

mutually_recursive_component(Key, Edges, Component) :-
    memberchk(edge(Key, _), Edges),
    findall(Other,
            ( member(edge(_, Other), Edges),
              path_to(Key, Other, Edges, [Key]),
              path_to(Other, Key, Edges, [Other])
            ),
            Reachable),
    sort([Key|Reachable], Component),
    length(Component, Size),
    Size > 1.

component_structural_measure(Predicates, Component, Argument) :-
    component_minimum_arity(Predicates, Component, MaxArgument),
    between(1, MaxArgument, Argument),
    component_recursive_calls(Predicates, Component, Calls),
    Calls = [_|_],
    maplist(decreases_structurally(Argument), Calls, _).

component_minimum_arity(Predicates, Component, MaxArgument) :-
    findall(Arity,
            ( member(mnn_pred(Key, _, _, _, _), Predicates),
              memberchk(Key, Component),
              Key = _/Arity
            ),
            Arities),
    min_list(Arities, MaxArgument).

component_recursive_calls(Predicates, Component, Calls) :-
    findall(PredicateCalls,
            ( member(mnn_pred(Key, _, _, Clauses, _), Predicates),
              memberchk(Key, Component),
              recursive_calls_in_clauses(Clauses, Component, PredicateCalls)
            ),
            NestedCalls),
    append(NestedCalls, Calls).

decreases_structurally(
    Argument, recursive_site(Id, Head, _, Call),
    decrease(Id, Call, structural(Argument))) :-
    arg(Argument, Head, HeadArgument),
    nonvar(HeadArgument),
    acyclic_term(HeadArgument),
    arg(Argument, Call, CallArgument),
    strict_subterm(CallArgument, HeadArgument).

decreases_naturally(
    Argument, recursive_site(Id, Head, Body, Call),
    decrease(Id, Call, natural(Argument))) :-
    arg(Argument, Head, Measure),
    var(Measure),
    arg(Argument, Call, Next),
    var(Next),
    Measure \== Next,
    conjunction_goals(Body, Goals),
    append(_, [integer(GuardedMeasure), PositiveGuard,
               is(AssignedNext, -(DecrementedMeasure, Step)),
               RecursiveCall|_], Goals),
    GuardedMeasure == Measure,
    PositiveGuard = >(PositiveMeasure, 0),
    PositiveMeasure == Measure,
    AssignedNext == Next,
    DecrementedMeasure == Measure,
    integer(Step),
    Step > 0,
    RecursiveCall == Call.

conjunction_goals(conj(Left, Right), Goals) :-
    !,
    conjunction_goals(Left, LeftGoals),
    conjunction_goals(Right, RightGoals),
    append(LeftGoals, RightGoals, Goals).
conjunction_goals(true, []) :-
    !.
conjunction_goals(Goal, [Goal]).

strict_subterm(Subterm, Term) :-
    compound(Term),
    functor(Term, _, Arity),
    between(1, Arity, Index),
    arg(Index, Term, Child),
    (   Child == Subterm
    ;   strict_subterm(Subterm, Child)
    ).

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

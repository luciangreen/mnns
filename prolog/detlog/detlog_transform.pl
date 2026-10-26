:- module(mnn_detlog_transform,
          [ transform_program/3
          ]).

:- use_module(library(lists)).

transform_program(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, TransformedPredicates, Proof, Trace),
    detlog_transform_report(Events)) :-
    transform_predicates(Predicates, Predicates, TransformedPredicates, Events).

transform_predicates([], _, [], []).
transform_predicates(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    SourcePredicates,
    [mnn_pred(Key, Modes, Domains, TransformedClauses, Status)|Transformed],
    Events) :-
    transform_clauses(Clauses, Key, SourcePredicates,
                      TransformedClauses, ClauseEvents),
    transform_predicates(Predicates, SourcePredicates,
                         Transformed, PredicateEvents),
    append(ClauseEvents, PredicateEvents, Events).

transform_clauses([], _, _, [], []).
transform_clauses(
    [mnn_clause(Id, Head, conj(Guard, !), Location)], Key,
    SourcePredicates,
    [mnn_clause(Id, Head, TransformedGuard, Location)],
    Events) :-
    deterministic_guard(Guard, SourcePredicates),
    !,
    transform_goal(Guard, Key, Id, SourcePredicates,
                   TransformedGuard, GuardEvents),
    append(GuardEvents, [removed_green_cut(Key, Id)], Events).
transform_clauses(
    [mnn_clause(Id, Head, conj(Guard, !), Location)], Key,
    SourcePredicates,
    [mnn_clause(Id, Head, ite(TransformedGuard, true, fail), Location)],
    Events) :-
    supported_cut_guard(Guard),
    !,
    transform_goal(Guard, Key, Id, SourcePredicates,
                   TransformedGuard, GuardEvents),
    append(GuardEvents, [compiled_cut(Key, Id, Guard)], Events).
transform_clauses(
    [mnn_clause(Id, Head, Body, Location)|Clauses], Key,
    SourcePredicates,
    [mnn_clause(Id, Head, TransformedBody, Location)|Transformed],
    Events) :-
    transform_goal(Body, Key, Id, SourcePredicates,
                   TransformedBody, ClauseEvents),
    transform_clauses(Clauses, Key, SourcePredicates,
                      Transformed, OtherEvents),
    append(ClauseEvents, OtherEvents, Events).

transform_goal(once(Goal), Key, Id, SourcePredicates,
               ite(Condition, true, fail),
               [compiled_once(Key, Id, Goal)|Events]) :-
    pure_goal(Goal, SourcePredicates),
    !,
    transform_goal(Goal, Key, Id, SourcePredicates, Condition, Events).
transform_goal(once(Goal), Key, Id, _, once(Goal),
               [kept_once(Key, Id, unsupported_goal(Goal))]) :-
    !.
transform_goal(conj(Left, Right), Key, Id, SourcePredicates,
               conj(NewLeft, NewRight), Events) :-
    !,
    transform_goal(Left, Key, Id, SourcePredicates, NewLeft, LeftEvents),
    transform_goal(Right, Key, Id, SourcePredicates, NewRight, RightEvents),
    append(LeftEvents, RightEvents, Events).
transform_goal(disj(Left, Right), Key, Id, SourcePredicates,
               disj(NewLeft, NewRight), Events) :-
    !,
    transform_goal(Left, Key, Id, SourcePredicates, NewLeft, LeftEvents),
    transform_goal(Right, Key, Id, SourcePredicates, NewRight, RightEvents),
    append(LeftEvents, RightEvents, Events).
transform_goal(ite(If, Then, Else), Key, Id, SourcePredicates,
               ite(NewIf, NewThen, NewElse), Events) :-
    !,
    transform_goal(If, Key, Id, SourcePredicates, NewIf, IfEvents),
    transform_goal(Then, Key, Id, SourcePredicates, NewThen, ThenEvents),
    transform_goal(Else, Key, Id, SourcePredicates, NewElse, ElseEvents),
    append([IfEvents, ThenEvents, ElseEvents], Events).
transform_goal(not(Goal), Key, Id, SourcePredicates, not(NewGoal), Events) :-
    !,
    transform_goal(Goal, Key, Id, SourcePredicates, NewGoal, Events).
transform_goal(Goal, _, _, _, Goal, []).

deterministic_guard(true, _).
deterministic_guard(conj(Left, Right), Predicates) :-
    !,
    deterministic_guard(Left, Predicates),
    deterministic_guard(Right, Predicates).
deterministic_guard(Goal, Predicates) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    Key = Name/Arity,
    deterministic_builtin(Key),
    \+ source_predicate(Predicates, Key).

deterministic_builtin((=)/2).
deterministic_builtin((\=)/2).
deterministic_builtin((==)/2).
deterministic_builtin((\==)/2).
deterministic_builtin(is/2).
deterministic_builtin((>)/2).
deterministic_builtin((>=)/2).
deterministic_builtin((<)/2).
deterministic_builtin((=<)/2).
deterministic_builtin((=:=)/2).
deterministic_builtin((=\=)/2).
deterministic_builtin(var/1).
deterministic_builtin(nonvar/1).
deterministic_builtin(atom/1).
deterministic_builtin(atomic/1).
deterministic_builtin(compound/1).
deterministic_builtin(ground/1).
deterministic_builtin(integer/1).
deterministic_builtin(number/1).
deterministic_builtin(is_list/1).

supported_cut_guard(Guard) :-
    nonvar(Guard),
    \+ goal_contains_cut(Guard),
    \+ explicit_call_in(Guard).

goal_contains_cut(!).
goal_contains_cut(conj(Left, Right)) :-
    (   goal_contains_cut(Left)
    ;   goal_contains_cut(Right)
    ).
goal_contains_cut(disj(Left, Right)) :-
    (   goal_contains_cut(Left)
    ;   goal_contains_cut(Right)
    ).
goal_contains_cut(ite(If, Then, Else)) :-
    (   goal_contains_cut(If)
    ;   goal_contains_cut(Then)
    ;   goal_contains_cut(Else)
    ).
goal_contains_cut(not(Goal)) :-
    goal_contains_cut(Goal).
goal_contains_cut(once(Goal)) :-
    goal_contains_cut(Goal).

explicit_call_in(Goal) :-
    sub_term(Subgoal, Goal),
    nonvar(Subgoal),
    functor(Subgoal, call, Arity),
    Arity > 0.

pure_goal(true, _) :-
    !.
pure_goal(fail, _) :-
    !.
pure_goal(conj(Left, Right), Predicates) :-
    !,
    pure_goal(Left, Predicates),
    pure_goal(Right, Predicates).
pure_goal(disj(Left, Right), Predicates) :-
    !,
    pure_goal(Left, Predicates),
    pure_goal(Right, Predicates).
pure_goal(ite(If, Then, Else), Predicates) :-
    !,
    pure_goal(If, Predicates),
    pure_goal(Then, Predicates),
    pure_goal(Else, Predicates).
pure_goal(not(Goal), Predicates) :-
    !,
    pure_goal(Goal, Predicates).
pure_goal(Goal, Predicates) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    Key = Name/Arity,
    pure_builtin(Key),
    \+ source_predicate(Predicates, Key).

source_predicate(Predicates, Key) :-
    member(mnn_pred(FoundKey, _, _, _, _), Predicates),
    FoundKey == Key.

pure_builtin((=)/2).
pure_builtin((\=)/2).
pure_builtin((==)/2).
pure_builtin((\==)/2).
pure_builtin(is/2).
pure_builtin((>)/2).
pure_builtin((>=)/2).
pure_builtin((<)/2).
pure_builtin((=<)/2).
pure_builtin((=:=)/2).
pure_builtin((=\=)/2).
pure_builtin(length/2).
pure_builtin(var/1).
pure_builtin(nonvar/1).
pure_builtin(atom/1).
pure_builtin(atomic/1).
pure_builtin(compound/1).
pure_builtin(ground/1).
pure_builtin(integer/1).
pure_builtin(number/1).
pure_builtin(is_list/1).
pure_builtin(between/3).
pure_builtin(nth0/3).
pure_builtin(nth1/3).
pure_builtin(member/2).
pure_builtin(append/3).
pure_builtin(select/3).

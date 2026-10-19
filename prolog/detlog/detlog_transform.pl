:- module(mnn_detlog_transform,
          [ transform_program/3
          ]).

:- use_module(library(lists)).

transform_program(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, TransformedPredicates, Proof, Trace),
    detlog_transform_report(Events)) :-
    transform_predicates(Predicates, TransformedPredicates, Events).

transform_predicates([], [], []).
transform_predicates(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    [mnn_pred(Key, Modes, Domains, TransformedClauses, Status)|Transformed],
    Events) :-
    transform_clauses(Clauses, Key, TransformedClauses, ClauseEvents),
    transform_predicates(Predicates, Transformed, PredicateEvents),
    append(ClauseEvents, PredicateEvents, Events).

transform_clauses([], _, [], []).
transform_clauses(
    [mnn_clause(Id, Head, Body, Location)|Clauses], Key,
    [mnn_clause(Id, Head, TransformedBody, Location)|Transformed],
    Events) :-
    transform_goal(Body, Key, Id, TransformedBody, ClauseEvents),
    transform_clauses(Clauses, Key, Transformed, OtherEvents),
    append(ClauseEvents, OtherEvents, Events).

transform_goal(once(Goal), Key, Id, ite(Condition, true, fail),
               [compiled_once(Key, Id, Goal)|Events]) :-
    pure_goal(Goal),
    !,
    transform_goal(Goal, Key, Id, Condition, Events).
transform_goal(once(Goal), Key, Id, once(Goal),
               [kept_once(Key, Id, unsupported_goal(Goal))]) :-
    !.
transform_goal(conj(Left, Right), Key, Id, conj(NewLeft, NewRight), Events) :-
    !,
    transform_goal(Left, Key, Id, NewLeft, LeftEvents),
    transform_goal(Right, Key, Id, NewRight, RightEvents),
    append(LeftEvents, RightEvents, Events).
transform_goal(disj(Left, Right), Key, Id, disj(NewLeft, NewRight), Events) :-
    !,
    transform_goal(Left, Key, Id, NewLeft, LeftEvents),
    transform_goal(Right, Key, Id, NewRight, RightEvents),
    append(LeftEvents, RightEvents, Events).
transform_goal(ite(If, Then, Else), Key, Id, ite(NewIf, NewThen, NewElse),
               Events) :-
    !,
    transform_goal(If, Key, Id, NewIf, IfEvents),
    transform_goal(Then, Key, Id, NewThen, ThenEvents),
    transform_goal(Else, Key, Id, NewElse, ElseEvents),
    append([IfEvents, ThenEvents, ElseEvents], Events).
transform_goal(not(Goal), Key, Id, not(NewGoal), Events) :-
    !,
    transform_goal(Goal, Key, Id, NewGoal, Events).
transform_goal(Goal, _, _, Goal, []).

pure_goal(true) :-
    !.
pure_goal(fail) :-
    !.
pure_goal(conj(Left, Right)) :-
    !,
    pure_goal(Left),
    pure_goal(Right).
pure_goal(disj(Left, Right)) :-
    !,
    pure_goal(Left),
    pure_goal(Right).
pure_goal(ite(If, Then, Else)) :-
    !,
    pure_goal(If),
    pure_goal(Then),
    pure_goal(Else).
pure_goal(not(Goal)) :-
    !,
    pure_goal(Goal).
pure_goal(Goal) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    pure_builtin(Name/Arity).

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
pure_builtin(var/1).
pure_builtin(nonvar/1).
pure_builtin(atom/1).
pure_builtin(atomic/1).
pure_builtin(compound/1).
pure_builtin(ground/1).
pure_builtin(integer/1).
pure_builtin(number/1).
pure_builtin(is_list/1).

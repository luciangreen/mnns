:- module(prolog2ann_normalise,
          [ normalize_program/2,
            check_stratification/1
          ]).

:- use_module(library(lists)).

%% normalize_program(+Parsed, -Program) is det.
%
%  Split disjunctions, flatten conjunctions, order arithmetic goals, and check
%  that negation is stratified.
%
%  @example
%    ?- normalize_program(ann_source('rules.pl', Clauses, []), Program).
normalize_program(ann_source(File, Clauses, Domains),
                  ann_program(File, Normalized, Domains)) :-
    expand_clauses(Clauses, Normalized),
    check_stratification(Normalized).

expand_clauses([], []).
expand_clauses([ann_clause(Id, Head, Body, Names, File, Line)|Clauses],
               Normalized) :-
    expand_body(Body, Alternatives),
    number_alternatives(Alternatives, Id, Head, Names, File, Line, Expanded),
    expand_clauses(Clauses, Rest),
    append(Expanded, Rest, Normalized).

number_alternatives([], _, _, _, _, _, []) :-
    !.
number_alternatives([Goals|Alternatives], Id, Head, Names, File, Line,
                    Expanded) :-
    number_alternatives([Goals|Alternatives], 1, Id, Head, Names, File, Line,
                        Expanded).

number_alternatives([], _, _, _, _, _, _, []) :-
    !.
number_alternatives([Goals|Alternatives], Index, Id, Head, Names, File, Line,
                    [ann_clause(Id-Index, Head, OrderedGoals, Names, File, Line)
                     |Rest]) :-
    NextIndex is Index + 1,
    number_alternatives(Alternatives, NextIndex, Id, Head, Names, File, Line,
                        Rest),
    order_arithmetic(Goals, OrderedGoals).

expand_body((Left ; Right), Alternatives) :-
    !,
    expand_body(Left, LeftAlternatives),
    expand_body(Right, RightAlternatives),
    append(LeftAlternatives, RightAlternatives, Alternatives).
expand_body((Left, Right), Alternatives) :-
    !,
    expand_body(Left, LeftAlternatives),
    expand_body(Right, RightAlternatives),
    cartesian_goals(LeftAlternatives, RightAlternatives, Alternatives).
expand_body(true, [[]]) :-
    !.
expand_body(Goal, [[Normalized]]) :-
    normalize_goal(Goal, Normalized).

cartesian_goals([], _, []).
cartesian_goals([Left|Lefts], Rights, Alternatives) :-
    append_goals(Left, Rights, First),
    cartesian_goals(Lefts, Rights, Rest),
    append(First, Rest, Alternatives).

append_goals(_, [], []).
append_goals(Left, [Right|Rights], [Combined|Rest]) :-
    append(Left, Right, Combined),
    append_goals(Left, Rights, Rest).

normalize_goal(\+ Goal, not(Goal)) :-
    !.
normalize_goal(not(Goal), not(Goal)) :-
    !.
normalize_goal(Goal, Goal).

order_arithmetic(Goals, Ordered) :-
    partition(arithmetic_goal, Goals, Arithmetic, Other),
    append(Other, Arithmetic, Ordered).

arithmetic_goal(Goal) :-
    functor(Goal, Name, Arity),
    (   Name == is, Arity == 2
    ;   memberchk(Name/Arity,
                  [ '<'/2, '=<'/2, '>'/2, '>='/2,
                    '=:='/2, '=\\='/2 ])
    ).

%% check_stratification(+NormalizedClauses) is det.
%
%  Throw `error(non_stratified_negation(Cycle), file(File, Line))` if a cycle
%  contains a negative dependency.
%
%  @example
%    ?- check_stratification(NormalizedClauses).
check_stratification(Clauses) :-
    dependency_edges(Clauses, Edges),
    (   member(dep(From, To, negative, File, Line), Edges),
        dependency_path(To, From, Edges, Path)
    ->  Cycle = [From|Path],
        throw(error(non_stratified_negation(Cycle), file(File, Line)))
    ;   true
    ).

dependency_edges([], []).
dependency_edges([ann_clause(_, Head, Goals, _, File, Line)|Clauses], Edges) :-
    predicate_indicator(Head, HeadPI),
    dependencies(Goals, HeadPI, File, Line, Current),
    dependency_edges(Clauses, Rest),
    append(Current, Rest, Edges).

dependencies([], _, _, _, []).
dependencies([not(Goal)|Goals], Head, File, Line,
             [dep(Head, Body, negative, File, Line)|Edges]) :-
    !,
    predicate_indicator(Goal, Body),
    dependencies(Goals, Head, File, Line, Edges).
dependencies([Goal|Goals], Head, File, Line, Edges) :-
    (   dependency_goal(Goal)
    ->  predicate_indicator(Goal, Body),
        Edges = [dep(Head, Body, positive, File, Line)|Rest]
    ;   Edges = Rest
    ),
    dependencies(Goals, Head, File, Line, Rest).

dependency_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    \+ built_in_dependency(Name, Arity).

built_in_dependency(true, 0).
built_in_dependency(fail, 0).
built_in_dependency(false, 0).
built_in_dependency('=', 2).
built_in_dependency('\\=', 2).
built_in_dependency('==', 2).
built_in_dependency('\\==', 2).
built_in_dependency(is, 2).
built_in_dependency('<', 2).
built_in_dependency('=<', 2).
built_in_dependency('>', 2).
built_in_dependency('>=', 2).
built_in_dependency('=:=', 2).
built_in_dependency('=\\=', 2).

predicate_indicator(Goal, Name/Arity) :-
    functor(Goal, Name, Arity).

dependency_path(Start, Target, Edges, Path) :-
    dependency_path(Start, Target, Edges, [Start], Path).

dependency_path(Target, Target, _, _, [Target]) :-
    !.
dependency_path(Current, Target, Edges, Seen, [Current|Path]) :-
    member(dep(Current, Next, _, _, _), Edges),
    \+ memberchk(Next, Seen),
    dependency_path(Next, Target, Edges, [Next|Seen], Path).

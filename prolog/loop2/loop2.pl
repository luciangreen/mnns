:- module(mnn_loop2,
          [ convert_program/3
          ]).

:- use_module('../ir/ir').
:- use_module(library(lists)).

convert_program(
    mnn_program(Name, meta(Source, Events), Predicates, Proof, Trace),
    mnn_program(Name, meta(Source, UpdatedEvents), UpdatedPredicates,
                Proof, Trace),
    loop2_report(Conversions)) :-
    max_clause_id(Predicates, MaxClauseId),
    NextClauseId is MaxClauseId + 1,
    convert_predicates(Predicates, Predicates, NextClauseId, 1,
                       [], ConvertedPredicates, [], GeneratedPredicates,
                       [], Conversions),
    append(ConvertedPredicates, GeneratedPredicates, UpdatedPredicates),
    generated_clause_events(GeneratedPredicates, GeneratedEvents),
    append(Events, GeneratedEvents, UpdatedEvents).

convert_predicates([], _, _, _, Converted, Converted,
                   Generated, Generated, Conversions, Conversions).
convert_predicates(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    SourcePredicates, NextClauseId, NextName,
    Converted0, Converted,
    Generated0, Generated,
    Conversions0, Conversions) :-
    convert_clauses(Clauses, SourcePredicates, NextClauseId, NextName,
                    NextClauseId1, NextName1, [], UpdatedClauses,
                    Generated0, Generated1, Conversions0, Conversions1),
    append(Converted0,
           [mnn_pred(Key, Modes, Domains, UpdatedClauses, Status)],
           Converted1),
    convert_predicates(Predicates, SourcePredicates, NextClauseId1, NextName1,
                       Converted1, Converted,
                       Generated1, Generated,
                       Conversions1, Conversions).

convert_clauses([], _, NextClauseId, NextName,
                NextClauseId, NextName, Clauses, Clauses,
                Generated, Generated, Conversions, Conversions).
convert_clauses(
    [mnn_clause(Id, Head, Body, Location)|Clauses],
    SourcePredicates, NextClauseId0, NextName0,
    NextClauseId, NextName, Clauses0, UpdatedClauses,
    Generated0, Generated, Conversions0, Conversions) :-
    convert_goal(Body, SourcePredicates, NextClauseId0, NextName0,
                 NextClauseId1, NextName1, UpdatedBody,
                 ClauseGenerated, ClauseConversions),
    append(Clauses0, [mnn_clause(Id, Head, UpdatedBody, Location)], Clauses1),
    append(Generated0, ClauseGenerated, Generated1),
    append(Conversions0, ClauseConversions, Conversions1),
    convert_clauses(Clauses, SourcePredicates, NextClauseId1, NextName1,
                    NextClauseId, NextName, Clauses1, UpdatedClauses,
                    Generated1, Generated, Conversions1, Conversions).

convert_goal(conj(Left, Right), Predicates, NextClauseId0, NextName0,
             NextClauseId, NextName, conj(NewLeft, NewRight),
             Generated, Conversions) :-
    !,
    convert_goal(Left, Predicates, NextClauseId0, NextName0,
                 NextClauseId1, NextName1, NewLeft,
                 LeftGenerated, LeftConversions),
    convert_goal(Right, Predicates, NextClauseId1, NextName1,
                 NextClauseId, NextName, NewRight,
                 RightGenerated, RightConversions),
    append(LeftGenerated, RightGenerated, Generated),
    append(LeftConversions, RightConversions, Conversions).
convert_goal(disj(Left, Right), Predicates, NextClauseId0, NextName0,
             NextClauseId, NextName, disj(NewLeft, NewRight),
             Generated, Conversions) :-
    !,
    convert_goal(Left, Predicates, NextClauseId0, NextName0,
                 NextClauseId1, NextName1, NewLeft,
                 LeftGenerated, LeftConversions),
    convert_goal(Right, Predicates, NextClauseId1, NextName1, NewRight,
                 NextClauseId, NextName, RightGenerated, RightConversions),
    append(LeftGenerated, RightGenerated, Generated),
    append(LeftConversions, RightConversions, Conversions).
convert_goal(ite(If, Then, Else), Predicates, NextClauseId0, NextName0,
             NextClauseId, NextName, ite(NewIf, NewThen, NewElse),
             Generated, Conversions) :-
    !,
    convert_goal(If, Predicates, NextClauseId0, NextName0,
                 NextClauseId1, NextName1, NewIf,
                 IfGenerated, IfConversions),
    convert_goal(Then, Predicates, NextClauseId1, NextName1,
                 NextClauseId2, NextName2, NewThen,
                 ThenGenerated, ThenConversions),
    convert_goal(Else, Predicates, NextClauseId2, NextName2,
                 NextClauseId, NextName, NewElse,
                 ElseGenerated, ElseConversions),
    append([IfGenerated, ThenGenerated, ElseGenerated], Generated),
    append([IfConversions, ThenConversions, ElseConversions], Conversions).
convert_goal(not(Goal), Predicates, NextClauseId0, NextName0,
             NextClauseId, NextName, not(NewGoal),
             Generated, Conversions) :-
    !,
    convert_goal(Goal, Predicates, NextClauseId0, NextName0,
                 NextClauseId, NextName, NewGoal, Generated, Conversions).
convert_goal(findall(Template, Goal, Results), Predicates,
             NextClauseId0, NextName0, NextClauseId, NextName,
             LoopCall, Generated,
             [conversion(findall_to_fold, helper(Loop/2),
                         side_conditions(finite_ground_facts(Count),
                                         deterministic_loop))]) :-
    finite_fact_values(Predicates, Goal, Template, Values),
    !,
    fresh_loop_name(NextName0, Predicates, Loop, NextName),
    LoopCall =.. [Loop, Values, Results],
    make_loop_predicate(Loop, NextClauseId0, Generated),
    NextClauseId is NextClauseId0 + 2,
    length(Values, Count).
convert_goal(Goal, _, NextClauseId, NextName,
             NextClauseId, NextName, Goal, [], []).

finite_fact_values(Predicates, Goal, Template, Values) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    Key = Name/Arity,
    member(mnn_pred(FoundKey, _, _, Clauses, _), Predicates),
    FoundKey == Key,
    maplist(ground_fact_clause, Clauses),
    fact_clause_values(Clauses, Goal, Template, Values),
    !.

ground_fact_clause(mnn_clause(_, Head, true, _)) :-
    ground(Head).

fact_clause_values([], _, _, []).
fact_clause_values([mnn_clause(_, Head, _, _)|Clauses],
                   Goal, Template, Values) :-
    copy_term((Goal, Template), (GoalCopy, TemplateCopy)),
    (   GoalCopy = Head
    ->  ground(TemplateCopy),
        Values = [TemplateCopy|Rest]
    ;   Values = Rest
    ),
    fact_clause_values(Clauses, Goal, Template, Rest).

fresh_loop_name(Index, Predicates, Name, NextIndex) :-
    format(atom(Candidate), 'mnn_loop2_~d', [Index]),
    (   member(mnn_pred(Key, _, _, _, _), Predicates),
        Key == Candidate/2
    ->  Next is Index + 1,
        fresh_loop_name(Next, Predicates, Name, NextIndex)
    ;   Name = Candidate,
        NextIndex is Index + 1
    ).

make_loop_predicate(Name, FirstId,
                    [mnn_pred(Name/2, ['?', '?'], [any, any],
                              [mnn_clause(FirstId, EmptyHead, true,
                                          generated(loop2)),
                               mnn_clause(SecondId, RecursiveHead,
                                          RecursiveBody,
                                          generated(loop2))],
                              generated(loop2))]) :-
    EmptyHead =.. [Name, [], []],
    RecursiveHead =.. [Name, [Value|Values], [Value|Results]],
    RecursiveBody =.. [Name, Values, Results],
    SecondId is FirstId + 1.

max_clause_id(Predicates, Max) :-
    findall(Id,
            ( member(mnn_pred(_, _, _, Clauses, _), Predicates),
              member(mnn_clause(Id, _, _, _), Clauses)
            ),
            Ids),
    (   Ids = []
    ->  Max = 0
    ;   max_list(Ids, Max)
    ).

generated_clause_events([], []).
generated_clause_events([mnn_pred(_, _, _, Clauses, _)|Predicates], Events) :-
    maplist(clause_event, Clauses, ClauseEvents),
    generated_clause_events(Predicates, RestEvents),
    append(ClauseEvents, RestEvents, Events).

clause_event(mnn_clause(Id, _, _, _), clause(Id)).

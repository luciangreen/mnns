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
                         side_conditions(GeneratorCondition,
                                         safe_arithmetic_filters(FilterCount),
                                         deterministic_loop))]) :-
    finite_generator_values(Predicates, Goal, Template, Values,
                            GeneratorKind, Count, FilterCount),
    !,
    GeneratorCondition =.. [GeneratorKind, Count],
    fresh_loop_name(NextName0, Predicates, Loop, NextName),
    LoopCall =.. [Loop, Values, Results],
    make_loop_predicate(Loop, NextClauseId0, Generated),
    NextClauseId is NextClauseId0 + 2.
convert_goal(Goal, _, NextClauseId, NextName,
             NextClauseId, NextName, Goal, [], []).

finite_generator_values(Predicates, Generator, Template, Values,
                        finite_ground_facts, Count, FilterCount) :-
    generator_parts(Generator, Goal, Filters),
    maplist(supported_filter, Filters),
    length(Filters, FilterCount),
    nonvar(Goal),
    callable(Goal),
    \+ predicate_property(system:Goal, built_in),
    functor(Goal, Name, Arity),
    Key = Name/Arity,
    member(mnn_pred(FoundKey, _, _, Clauses, _), Predicates),
    FoundKey == Key,
    maplist(ground_fact_clause, Clauses),
    fact_clause_values(Clauses, Goal, Template, Filters, Values, Count),
    !.
finite_generator_values(_, Generator, Template, Values,
                        finite_ground_member, Count, FilterCount) :-
    generator_parts(Generator, member(Value, List), Filters),
    ground(List),
    is_list(List),
    maplist(supported_filter, Filters),
    length(Filters, FilterCount),
    member_candidate_values(List, Value, Template, Filters, Values),
    length(List, Count),
    !.
finite_generator_values(_, Generator, Template, Values,
                        finite_ground_between, Count, FilterCount) :-
    generator_parts(Generator, between(Low, High, Value), Filters),
    integer(Low),
    integer(High),
    (var(Value) ; integer(Value)),
    maplist(supported_filter, Filters),
    length(Filters, FilterCount),
    between_values(Low, High, Value, Template, Filters, Values, Count),
    !.
finite_generator_values(_, Generator, Template, Values,
                        finite_ground_nth0, Count, FilterCount) :-
    generator_parts(Generator, nth0(Index, List, Value), Filters),
    ground(List),
    is_list(List),
    supported_nth_index(Index),
    maplist(supported_filter, Filters),
    length(Filters, FilterCount),
    length(List, Count),
    nth_candidate_values(List, 0, Index, Value, Template, Filters, Values),
    !.
finite_generator_values(_, Generator, Template, Values,
                        finite_ground_nth1, Count, FilterCount) :-
    generator_parts(Generator, nth1(Index, List, Value), Filters),
    ground(List),
    is_list(List),
    supported_nth_index(Index),
    maplist(supported_filter, Filters),
    length(Filters, FilterCount),
    length(List, Count),
    nth_candidate_values(List, 1, Index, Value, Template, Filters, Values),
    !.

supported_nth_index(Index) :-
    var(Index),
    !.
supported_nth_index(Index) :-
    integer(Index).

nth_candidate_values([], _, _, _, _, _, []).
nth_candidate_values([Candidate|Candidates], Index, IndexPattern,
                     ValuePattern, Template, Filters, Values) :-
    copy_term((IndexPattern, ValuePattern, Template, Filters),
              (IndexCopy, ValueCopy, TemplateCopy, FiltersCopy)),
    (   IndexCopy = Index,
        ValueCopy = Candidate
    ->  evaluate_filters(FiltersCopy, FilterResult),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   Values = Rest
    ),
    NextIndex is Index + 1,
    nth_candidate_values(Candidates, NextIndex, IndexPattern,
                         ValuePattern, Template, Filters, Rest).

between_values(Low, High, Value, Template, Filters, Values, Count) :-
    (   Low > High
    ->  Candidates = [],
        Count = 0
    ;   Count is High - Low + 1,
        Count =< 10000,
        findall(Number, between(Low, High, Number), Candidates)
    ),
    between_candidate_values(Candidates, Value, Template, Filters, Values).

between_candidate_values([], _, _, _, []).
between_candidate_values([Number|Numbers], Value, Template, Filters, Values) :-
    copy_term((Value, Template, Filters),
              (ValueCopy, TemplateCopy, FiltersCopy)),
    (   ValueCopy = Number
    ->  evaluate_filters(FiltersCopy, FilterResult),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   Values = Rest
    ),
    between_candidate_values(Numbers, Value, Template, Filters, Rest).

generator_parts(Generator, Goal, Filters) :-
    flatten_conjunction(Generator, [Goal|Filters]).

flatten_conjunction(conj(Left, Right), Goals) :-
    !,
    flatten_conjunction(Left, LeftGoals),
    flatten_conjunction(Right, RightGoals),
    append(LeftGoals, RightGoals, Goals).
flatten_conjunction((Left, Right), Goals) :-
    !,
    flatten_conjunction(Left, LeftGoals),
    flatten_conjunction(Right, RightGoals),
    append(LeftGoals, RightGoals, Goals).
flatten_conjunction(Goal, [Goal]).

ground_fact_clause(mnn_clause(_, Head, true, _)) :-
    ground(Head).

supported_filter(Filter) :-
    nonvar(Filter),
    functor(Filter, Name, 2),
    memberchk(Name, [>, >=, <, =<, =:=, =\=]),
    arg(1, Filter, Left),
    arg(2, Filter, Right),
    arithmetic_expression(Left),
    arithmetic_expression(Right).

arithmetic_expression(Expression) :-
    number(Expression),
    !.
arithmetic_expression(Expression) :-
    var(Expression),
    !.
arithmetic_expression(Expression) :-
    compound(Expression),
    compound_name_arguments(Expression, Name, Arguments),
    arithmetic_operator(Name, Arity),
    length(Arguments, Arity),
    maplist(arithmetic_expression, Arguments).

arithmetic_operator(+, 1).
arithmetic_operator(-, 1).
arithmetic_operator(abs, 1).
arithmetic_operator(+, 2).
arithmetic_operator(-, 2).
arithmetic_operator(*, 2).
arithmetic_operator(/, 2).
arithmetic_operator(//, 2).
arithmetic_operator(mod, 2).
arithmetic_operator(rem, 2).

fact_clause_values([], _, _, _, [], 0).
fact_clause_values([mnn_clause(_, Head, _, _)|Clauses],
                   Goal, Template, Filters, Values, Count) :-
    copy_term((Goal, Template, Filters),
              (GoalCopy, TemplateCopy, FiltersCopy)),
    (   GoalCopy = Head
    ->  evaluate_filters(FiltersCopy, FilterResult),
        fact_clause_values(Clauses, Goal, Template, Filters, Rest, RestCount),
        Count is RestCount + 1,
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   fact_clause_values(Clauses, Goal, Template, Filters, Values, Count)
    ).

member_candidate_values([], _, _, _, []).
member_candidate_values([Candidate|Candidates], Value, Template, Filters, Values) :-
    copy_term((Value, Template, Filters),
              (ValueCopy, TemplateCopy, FiltersCopy)),
    (   ValueCopy = Candidate
    ->  evaluate_filters(FiltersCopy, FilterResult),
        member_candidate_values(Candidates, Value, Template, Filters, Rest),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   member_candidate_values(Candidates, Value, Template, Filters, Values)
    ).

evaluate_filters([], true).
evaluate_filters([Filter|Filters], Result) :-
    evaluate_filter(Filter, FilterResult),
    (   FilterResult == true
    ->  evaluate_filters(Filters, Result)
    ;   Result = false
    ).

evaluate_filter(Filter, Result) :-
    Filter =.. [Name, Left, Right],
    arithmetic_value(Left, LeftValue),
    arithmetic_value(Right, RightValue),
    compare_values(Name, LeftValue, RightValue, Result).

arithmetic_value(Expression, Value) :-
    arithmetic_expression(Expression),
    ground(Expression),
    catch(Value is Expression, _, fail).

compare_values(>, Left, Right, Result) :-
    comparison_result(Left > Right, Result).
compare_values(>=, Left, Right, Result) :-
    comparison_result(Left >= Right, Result).
compare_values(<, Left, Right, Result) :-
    comparison_result(Left < Right, Result).
compare_values(=<, Left, Right, Result) :-
    comparison_result(Left =< Right, Result).
compare_values(=:=, Left, Right, Result) :-
    comparison_result(Left =:= Right, Result).
compare_values(=\=, Left, Right, Result) :-
    comparison_result(Left =\= Right, Result).

comparison_result(Comparison, Result) :-
    (   call(Comparison)
    ->  Result = true
    ;   Result = false
    ).

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

:- module(mnn_detlog,
          [ analyze_determinism/2
          ]).

:- use_module(library(lists)).

analyze_determinism(
    mnn_program(_, _, Predicates, _, _),
    detlog_report(Results)) :-
    maplist(analyze_predicate(Predicates), Predicates, Results).

analyze_predicate(Predicates,
                  mnn_pred(Key, _, _, Clauses, _),
                  predicate(Key, mode(all_arguments_unbound),
                            Determinism, Evidence)) :-
    maplist(clause_outcomes(Predicates, [Key]), Clauses, ClauseOutcomes),
    (   member(clause_outcome(_, unavailable(Reason)), ClauseOutcomes)
    ->  Determinism = unavailable(Reason),
        Evidence = unsupported_body
    ;   predicate_outcomes(Clauses, ClauseOutcomes, Outcomes),
        outcomes_determinism(Outcomes, Class),
        Determinism = determinism(Class),
        Evidence = success_counts(Outcomes)
    ).

clause_outcomes(Predicates, Stack,
                mnn_clause(_, Head, Body, _),
                clause_outcome(Head, Outcomes)) :-
    goal_outcomes(Body, Predicates, Stack, Outcomes).

goal_outcomes(true, _, _, [1]) :-
    !.
goal_outcomes(fail, _, _, [0]) :-
    !.
goal_outcomes(conj(Left, Right), Predicates, Stack, Outcomes) :-
    !,
    goal_outcomes(Left, Predicates, Stack, LeftOutcomes),
    goal_outcomes(Right, Predicates, Stack, RightOutcomes),
    (   LeftOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   RightOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   product_outcomes(LeftOutcomes, RightOutcomes, Outcomes)
    ).
goal_outcomes(disj(Left, Right), Predicates, Stack, Outcomes) :-
    !,
    goal_outcomes(Left, Predicates, Stack, LeftOutcomes),
    goal_outcomes(Right, Predicates, Stack, RightOutcomes),
    (   LeftOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   RightOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   sum_outcomes(LeftOutcomes, RightOutcomes, Outcomes)
    ).
goal_outcomes(ite(Condition, Then, Else), Predicates, Stack, Outcomes) :-
    !,
    goal_outcomes(Condition, Predicates, Stack, ConditionOutcomes),
    goal_outcomes(Then, Predicates, Stack, ThenOutcomes),
    goal_outcomes(Else, Predicates, Stack, ElseOutcomes),
    (   ConditionOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   ThenOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   ElseOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   committed_outcomes(ConditionOutcomes, ThenOutcomes,
                           ElseOutcomes, Outcomes)
    ).
goal_outcomes(not(Goal), Predicates, Stack, Outcomes) :-
    !,
    goal_outcomes(Goal, Predicates, Stack, GoalOutcomes),
    (   GoalOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   negated_outcomes(GoalOutcomes, Outcomes)
    ).
goal_outcomes(once(Goal), Predicates, Stack, Outcomes) :-
    !,
    goal_outcomes(Goal, Predicates, Stack, GoalOutcomes),
    (   GoalOutcomes = unavailable(Reason)
    ->  Outcomes = unavailable(Reason)
    ;   once_outcomes(GoalOutcomes, Outcomes)
    ).
goal_outcomes(Goal, _, _, Outcomes) :-
    nonvar(Goal),
    Goal = between(Low, High, Value),
    integer(Low),
    integer(High),
    (   var(Value)
    ;   integer(Value)
    ),
    !,
    between_outcomes(Low, High, Value, Outcomes).
goal_outcomes(Goal, Predicates, _, Outcomes) :-
    nonvar(Goal),
    Goal = member(Value, List),
    ground(List),
    is_list(List),
    \+ member(mnn_pred(member/2, _, _, _, _), Predicates),
    !,
    member_outcomes(Value, List, Outcomes).
goal_outcomes(Goal, Predicates, _, Outcomes) :-
    nonvar(Goal),
    Goal = select(Value, List, Rest),
    ground(List),
    is_list(List),
    (   var(Value)
    ;   ground(Value)
    ),
    (   var(Rest)
    ;   ground(Rest)
    ),
    \+ member(mnn_pred(select/3, _, _, _, _), Predicates),
    !,
    select_outcomes(Value, List, Rest, Outcomes).
goal_outcomes(Goal, Predicates, _, Outcomes) :-
    nonvar(Goal),
    Goal = length(List, Length),
    ground(List),
    is_list(List),
    (   var(Length)
    ;   integer(Length),
        Length >= 0
    ),
    \+ member(mnn_pred(length/2, _, _, _, _), Predicates),
    !,
    list_length_outcomes(List, Length, Outcomes).
goal_outcomes(Goal, Predicates, _, Outcomes) :-
    nonvar(Goal),
    Goal = nth0(Index, List, Element),
    ground(List),
    is_list(List),
    (   var(Index)
    ;   integer(Index)
    ),
    (   var(Element)
    ;   ground(Element)
    ),
    (   var(Index)
    ->  Index \== Element
    ;   true
    ),
    \+ member(mnn_pred(nth0/3, _, _, _, _), Predicates),
    !,
    nth_list_outcomes(0, Index, List, Element, Outcomes).
goal_outcomes(Goal, Predicates, _, Outcomes) :-
    nonvar(Goal),
    Goal = nth1(Index, List, Element),
    ground(List),
    is_list(List),
    (   var(Index)
    ;   integer(Index)
    ),
    (   var(Element)
    ;   ground(Element)
    ),
    (   var(Index)
    ->  Index \== Element
    ;   true
    ),
    \+ member(mnn_pred(nth1/3, _, _, _, _), Predicates),
    !,
    nth_list_outcomes(1, Index, List, Element, Outcomes).
goal_outcomes(Goal, Predicates, _, Outcomes) :-
    nonvar(Goal),
    Goal = append(Prefix, Suffix, List),
    \+ member(mnn_pred(append/3, _, _, _, _), Predicates),
    append_ground_mode(Prefix, Suffix, List, Outcomes),
    !.
goal_outcomes(Goal, _, _, Outcomes) :-
    semidet_builtin(Goal),
    ground(Goal),
    !,
    ground_builtin_outcomes(Goal, Outcomes).
goal_outcomes(Goal, _, _, [0, 1]) :-
    semidet_builtin(Goal),
    !.
goal_outcomes(Goal, Predicates, _, [2]) :-
    nonvar(Goal),
    Goal = append(Prefix, Suffix, List),
    distinct_variables([Prefix, Suffix, List]),
    \+ member(mnn_pred(append/3, _, _, _, _), Predicates),
    !.
goal_outcomes(Goal, Predicates, Stack, Outcomes) :-
    user_predicate_goal(Goal, Predicates, Stack, Outcomes),
    !.
goal_outcomes(Goal, _, _, unavailable(unsupported_goal(Goal))).

user_predicate_goal(Goal, Predicates, Stack, Outcomes) :-
    nonvar(Goal),
    callable(Goal),
    Goal =.. [Name|Arguments],
    distinct_variables(Arguments),
    length(Arguments, Arity),
    Key = Name/Arity,
    member(mnn_pred(Key, _, _, Clauses, _), Predicates),
    !,
    (   memberchk(Key, Stack)
    ->  Outcomes = unavailable(recursive_call(Key))
    ;   NextStack = [Key|Stack],
      maplist(clause_outcomes(Predicates, NextStack), Clauses,
              ClauseOutcomes),
      (   member(clause_outcome(_, unavailable(Reason)), ClauseOutcomes)
      ->  Outcomes = unavailable(Reason)
      ;   predicate_outcomes(Clauses, ClauseOutcomes, Outcomes)
      )
    ).

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

ground_builtin_outcomes(Goal, Outcomes) :-
    catch((   call(Goal)
          ->  Outcomes = [1]
          ;   Outcomes = [0]
          ),
          Error,
          Outcomes = unavailable(exceptional_goal(Goal, Error))).

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

append_ground_mode(Prefix, Suffix, List, Outcomes) :-
    append_supported_list_mode([Prefix, Suffix, List]),
    copy_term((Prefix, Suffix, List), (PrefixCopy, SuffixCopy, ListCopy)),
    (   append(PrefixCopy, SuffixCopy, ListCopy)
    ->  Outcomes = [1]
    ;   Outcomes = [0]
    ).

append_supported_list_mode([Prefix, Suffix, List]) :-
    (   ground_proper_list(Prefix),
        ground_proper_list(Suffix),
        ground_proper_list(List)
    ;   var(Prefix),
        ground_proper_list(Suffix),
        ground_proper_list(List)
    ;   ground_proper_list(Prefix),
        var(Suffix),
        ground_proper_list(List)
    ;   ground_proper_list(Prefix),
        ground_proper_list(Suffix),
        var(List)
    ).

nth_list_outcomes(Offset, Index, List, Element, Outcomes) :-
    nth_list_success_count(List, Offset, Index, Element, 0, Count),
    (   Count =:= 0
    ->  Outcomes = [0]
    ;   Count =:= 1
    ->  Outcomes = [1]
    ;   Outcomes = [2]
    ).

nth_list_success_count([], _, _, _, Count, Count).
nth_list_success_count([Candidate|Candidates], Position, Index, Element,
                       Count0, Count) :-
    (   (var(Index) -> true ; Position =:= Index),
        (var(Element) -> true ; Element == Candidate)
    ->  Count1 is min(2, Count0 + 1)
    ;   Count1 = Count0
    ),
    (   Count1 =:= 2
    ->  Count = 2
    ;   NextPosition is Position + 1,
        nth_list_success_count(Candidates, NextPosition, Index, Element,
                               Count1, Count)
    ).

ground_proper_list(List) :-
    ground(List),
    is_list(List).

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

once_outcomes(GoalOutcomes, Outcomes) :-
    findall(Outcome,
            ( member(Count, GoalOutcomes),
              (   Count =:= 0
              ->  Outcome = 0
              ;   Outcome = 1
              )
            ),
            Possible),
    sort(Possible, Outcomes).

between_outcomes(Low, High, _, [0]) :-
    High < Low,
    !.
between_outcomes(Low, High, Value, Outcomes) :-
    (   var(Value)
    ->  Count is High - Low + 1,
        (   Count =:= 1
        ->  Outcomes = [1]
        ;   Outcomes = [2]
        )
    ;   Value >= Low,
        Value =< High
    ->  Outcomes = [1]
    ;   Outcomes = [0]
    ).

member_outcomes(Value, List, [0]) :-
    member_success_count(Value, List, 0, 0),
    !.
member_outcomes(Value, List, [1]) :-
    member_success_count(Value, List, 0, 1),
    !.
member_outcomes(Value, List, [2]) :-
    member_success_count(Value, List, 0, 2).

member_success_count(_, [], Count, Count).
member_success_count(Value, [Element|Elements], Count0, Count) :-
    (   member_value_matches(Value, Element)
    ->  Count1 is min(2, Count0 + 1)
    ;   Count1 = Count0
    ),
    (   Count1 =:= 2
    ->  Count = 2
    ;   member_success_count(Value, Elements, Count1, Count)
    ).

member_value_matches(Value, Element) :-
    copy_term(Value, ValueCopy),
    ValueCopy = Element.

select_outcomes(Value, List, Rest, Outcomes) :-
    select_success_count(List, [], Value, Rest, 0, Count),
    (   Count =:= 0
    ->  Outcomes = [0]
    ;   Count =:= 1
    ->  Outcomes = [1]
    ;   Outcomes = [2]
    ).

select_success_count([], _, _, _, Count, Count).
select_success_count([Element|Elements], Prefix, Value, Rest,
                     Count0, Count) :-
    reverse(Prefix, OrderedPrefix),
    append(OrderedPrefix, Elements, CandidateRest),
    (   copy_term((Value, Rest), (ValueCopy, RestCopy)),
        ValueCopy = Element,
        RestCopy = CandidateRest
    ->  Count1 is min(2, Count0 + 1)
    ;   Count1 = Count0
    ),
    (   Count1 =:= 2
    ->  Count = 2
    ;   select_success_count(Elements, [Element|Prefix], Value, Rest,
                             Count1, Count)
    ).

list_length_outcomes(_List, Length, [1]) :-
    var(Length),
    !.
list_length_outcomes(List, Length, Outcomes) :-
    length(List, ActualLength),
    (   Length =:= ActualLength
    ->  Outcomes = [1]
    ;   Outcomes = [0]
    ).

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

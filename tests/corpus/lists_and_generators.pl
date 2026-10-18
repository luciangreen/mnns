:- module(lists_and_generators,
          [ selected/2,
            indexed_values/2,
            one_based_indexed_values/2,
            bounded_values/3
          ]).

selected(Values, Selected) :-
    findall(Value,
            ( member(Value, Values),
              between(1, 10, Value),
              Value mod 2 =:= 0
            ),
            Selected).

indexed_values(Values, Pairs) :-
    findall(Index-Value, nth0(Index, Values, Value), Pairs).

one_based_indexed_values(Values, Pairs) :-
    findall(Index-Value, nth1(Index, Values, Value), Pairs).

bounded_values(Low, High, Values) :-
    findall(Value, between(Low, High, Value), Values).

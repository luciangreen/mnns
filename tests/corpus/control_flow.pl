:- module(control_flow, [classify/2, safe_lookup/3]).

classify(Value, positive) :-
    Value > 0,
    !.
classify(Value, Result) :-
    (   Value =:= 0
    ->  Result = zero
    ;   Result = negative
    ).

safe_lookup(List, Index, Value) :-
    (   integer(Index),
        Index >= 0,
        nth0(Index, List, Value)
    ;   \+ integer(Index),
        Value = invalid_index
    ).

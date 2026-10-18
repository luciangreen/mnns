:- module(builtins_and_arithmetic, [summarize/7, selected/2]).

summarize(Values, Length, First, Last, Extended, Total, Doubled) :-
    length(Values, Length),
    nth1(1, Values, First),
    nth1(Length, Values, Last),
    append(Values, [tail], Extended),
    total_values(Values, Total),
    Doubled is Total * 2.

total_values([], 0).
total_values([Head|Tail], Total) :-
    total_values(Tail, Rest),
    Total is Head + Rest.

selected(Values, Selected) :-
    findall(Value,
            ( member(Value, Values),
              between(1, 10, Value),
              Value mod 2 =:= 0
            ),
            Selected).

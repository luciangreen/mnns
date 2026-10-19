:- module(mnn_algebraplop,
          [ infer_sequence_formula/2
          ]).

infer_sequence_formula(Samples, Result) :-
    (   is_list(Samples),
        maplist(integer, Samples),
        length(Samples, Count),
        Count >= 3
    ->  infer_valid_sequence(Samples, Result)
    ;   Result = no_formula
    ),
    !.

infer_valid_sequence(Samples, formula(constant(Value), verified_on(Samples))) :-
    Samples = [Value|_],
    maplist(=(Value), Samples),
    !.
infer_valid_sequence(Samples, formula(linear(Slope, Intercept),
                                      verified_on(Samples))) :-
    Samples = [Intercept, Second|Rest],
    Slope is Second - Intercept,
    Next is Second + Slope,
    verify_affine(Rest, Next, Slope),
    !.
infer_valid_sequence(Samples,
                     formula(quadratic(Intercept, FirstDifference,
                                       SecondDifference),
                             verified_on(Samples))) :-
    Samples = [Intercept, Second, Third, Fourth|Rest],
    FirstDifference is Second - Intercept,
    NextDifference is Third - Second,
    SecondDifference is NextDifference - FirstDifference,
    FollowingDifference is NextDifference + SecondDifference,
    verify_quadratic([Fourth|Rest], Third, FollowingDifference,
                     SecondDifference),
    !.
infer_valid_sequence(Samples,
                     formula(exponential(Initial, Base), verified_on(Samples))) :-
    Samples = [Initial, Second|Rest],
    Initial =\= 0,
    0 is Second mod Initial,
    Base is Second // Initial,
    verify_geometric(Rest, Second, Base),
    !.
infer_valid_sequence(Samples,
                     formula(polynomial(Coefficients), verified_on(Samples))) :-
    length(Samples, Count),
    MaximumDegree is Count - 2,
    between(3, MaximumDegree, Degree),
    PrefixCount is Degree + 1,
    length(Prefix, PrefixCount),
    append(Prefix, HeldOut, Samples),
    forward_coefficients(Prefix, Coefficients),
    last(Coefficients, LeadingCoefficient),
    LeadingCoefficient =\= 0,
    verify_polynomial_samples(HeldOut, PrefixCount, Coefficients),
    !.
infer_valid_sequence(_, no_formula).

verify_affine([], _, _).
verify_affine([Value|Values], Expected, Slope) :-
    Value =:= Expected,
    Next is Expected + Slope,
    verify_affine(Values, Next, Slope).

verify_quadratic([], _, _, _).
verify_quadratic([Value|Values], Previous, Difference, SecondDifference) :-
    Expected is Previous + Difference,
    Value =:= Expected,
    NextDifference is Difference + SecondDifference,
    verify_quadratic(Values, Expected, NextDifference, SecondDifference).

verify_geometric([], _, _).
verify_geometric([Value|Values], Previous, Base) :-
    Expected is Previous * Base,
    Value =:= Expected,
    verify_geometric(Values, Value, Base).

forward_coefficients([Value], [Value]) :-
    !.
forward_coefficients(Values, [FirstDifference|Coefficients]) :-
    Values = [First|_],
    FirstDifference = First,
    adjacent_differences(Values, Differences),
    forward_coefficients(Differences, Coefficients).

adjacent_differences([_], []) :-
    !.
adjacent_differences([First, Second|Values], [Difference|Differences]) :-
    Difference is Second - First,
    adjacent_differences([Second|Values], Differences).

verify_polynomial_samples([], _, _).
verify_polynomial_samples([Sample|Samples], Position, Coefficients) :-
    newton_value(Coefficients, Position, Expected),
    Sample =:= Expected,
    NextPosition is Position + 1,
    verify_polynomial_samples(Samples, NextPosition, Coefficients).

newton_value(Coefficients, Position, Value) :-
    newton_value(Coefficients, Position, 0, 0, Value).

newton_value([], _, _, Value, Value).
newton_value([Coefficient|Coefficients], Position, Order, Accumulator, Value) :-
    binomial(Position, Order, Binomial),
    NextAccumulator is Accumulator + Coefficient * Binomial,
    NextOrder is Order + 1,
    newton_value(Coefficients, Position, NextOrder, NextAccumulator, Value).

binomial(_, 0, 1) :-
    !.
binomial(Number, Order, Value) :-
    Order > 0,
    Order =< Number,
    PreviousOrder is Order - 1,
    binomial(Number, PreviousOrder, Previous),
    Value is Previous * (Number - Order + 1) // Order.

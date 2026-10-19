:- module(mnn_algebraplop,
          [ infer_sequence_formula/2,
            invert_sequence_formula/3,
            evaluate_sequence_formula/3
          ]).

evaluate_sequence_formula(Formula, Position, Result) :-
    (   integer(Position),
        Position >= 0,
        Formula = formula(Shape, verified_on(_)),
        sequence_value(Shape, Position, Value)
    ->  Result = value(Value)
    ;   Result = no_value
    ),
    !.

sequence_value(constant(Value), _, Value) :-
    integer(Value).
sequence_value(linear(Slope, Intercept), Position, Value) :-
    integer(Slope),
    integer(Intercept),
    Value is Slope * Position + Intercept.
sequence_value(quadratic(Intercept, FirstDifference, SecondDifference),
               Position, Value) :-
    integer(Intercept),
    integer(FirstDifference),
    integer(SecondDifference),
    SecondOrderTerm is Position * (Position - 1) // 2,
    Value is Intercept + FirstDifference * Position +
            SecondDifference * SecondOrderTerm.
sequence_value(polynomial(Coefficients), Position, Value) :-
    is_list(Coefficients),
    Coefficients \= [],
    maplist(integer, Coefficients),
    newton_value(Coefficients, Position, Value).
sequence_value(exponential(Initial, Base), Position, Value) :-
    integer(Initial),
    integer(Base),
    integer_power(Base, Position, Power),
    Value is Initial * Power.

integer_power(_, 0, 1) :-
    !.
integer_power(Base, Exponent, Power) :-
    Exponent > 0,
    HalfExponent is Exponent // 2,
    integer_power(Base, HalfExponent, HalfPower),
    (   0 is Exponent mod 2
    ->  Power is HalfPower * HalfPower
    ;   Power is Base * HalfPower * HalfPower
    ).

invert_sequence_formula(Formula, Value, Result) :-
    (   integer(Value),
        Formula = formula(constant(Constant), verified_on(_)),
        integer(Constant)
    ->  (   Value =:= Constant
        ->  Result = all_positions
        ;   Result = no_position
        )
    ;   integer(Value),
        Formula = formula(linear(Slope, Intercept), verified_on(_)),
        integer(Slope),
        integer(Intercept)
    ->  inverse_linear_position(Slope, Intercept, Value, Result)
    ;   integer(Value),
        Formula = formula(exponential(Initial, Base), verified_on(_)),
        integer(Initial),
        integer(Base)
    ->  inverse_exponential_positions(Initial, Base, Value, Result)
    ;   integer(Value),
        Formula = formula(polynomial(Coefficients), verified_on(_)),
        is_list(Coefficients),
        maplist(integer, Coefficients),
        Coefficients \= []
    ->  inverse_polynomial_positions(Coefficients, Value, Result)
    ;   Result = no_position
    ),
    !.

inverse_linear_position(0, Intercept, Value, Result) :-
    !,
    (   Value =:= Intercept
    ->  Result = all_positions
    ;   Result = no_position
    ).
inverse_linear_position(Slope, Intercept, Value, Result) :-
    Difference is Value - Intercept,
    (   0 is Difference mod Slope
    ->  Position is Difference // Slope,
        (   Position >= 0
        ->  Result = position(Position)
        ;   Result = no_position
        )
    ;   Result = no_position
    ).

inverse_exponential_positions(0, _, 0, all_positions) :-
    !.
inverse_exponential_positions(0, _, _, no_position) :-
    !.
inverse_exponential_positions(Initial, 1, Value, Result) :-
    !,
    (   Value =:= Initial
    ->  Result = all_positions
    ;   Result = no_position
    ).
inverse_exponential_positions(Initial, -1, Value, Result) :-
    !,
    (   Value =:= Initial
    ->  Result = positions(0, 2)
    ;   NegatedInitial is -Initial,
    (   Value =:= NegatedInitial
    ->  Result = positions(1, 2)
    ;   Result = no_position
    )
    ).
inverse_exponential_positions(Initial, 0, Value, Result) :-
    !,
    (   Value =:= Initial
    ->  Result = position(0)
    ;   Value =:= 0
    ->  Result = positions(1, 1)
    ;   Result = no_position
    ).
inverse_exponential_positions(Initial, Base, Value, Result) :-
    (   geometric_position(Initial, Base, Value, Position)
    ->  Result = position(Position)
    ;   Result = no_position
    ).

geometric_position(Initial, _, Initial, 0) :-
    !.
geometric_position(Initial, Base, Value, Position) :-
    abs(Base) > 1,
    0 is Value mod Base,
    Quotient is Value // Base,
    geometric_position(Initial, Base, Quotient, PreviousPosition),
    Position is PreviousPosition + 1.

inverse_polynomial_positions(Coefficients, Value, Result) :-
    trim_newton_coefficients(Coefficients, Trimmed),
    (   Trimmed = [Constant]
    ->  (   Value =:= Constant
        ->  Result = all_positions
        ;   Result = no_position
        )
    ;   polynomial_root_bound(Trimmed, Value, Bound),
        findall(Position,
                ( between(0, Bound, Position),
                  newton_value(Trimmed, Position, Sample),
                  Sample =:= Value
                ),
                Positions),
        polynomial_positions_result(Positions, Result)
    ).

trim_newton_coefficients(Coefficients, Trimmed) :-
    reverse(Coefficients, Reversed),
    trim_reversed_coefficients(Reversed, TrimmedReversed),
    reverse(TrimmedReversed, Trimmed).

trim_reversed_coefficients([0|Coefficients], Trimmed) :-
    Coefficients \= [],
    !,
    trim_reversed_coefficients(Coefficients, Trimmed).
trim_reversed_coefficients(Coefficients, Coefficients).

polynomial_positions_result([], no_position).
polynomial_positions_result([Position], position(Position)) :-
    !.
polynomial_positions_result(Positions, positions(Positions)).

polynomial_root_bound(Coefficients, Value, Bound) :-
    length(Coefficients, Count),
    Degree is Count - 1,
    factorial(Degree, DegreeFactorial),
    newton_monomial_terms(Coefficients, 0, Degree, DegreeFactorial, Terms),
    sum_polynomials(Terms, [], ScaledPolynomial),
    ScaledPolynomial = [Constant|OtherCoefficients],
    AdjustedConstant is Constant - Value * DegreeFactorial,
    MonomialCoefficients = [AdjustedConstant|OtherCoefficients],
    reverse(MonomialCoefficients, [LeadingCoefficient|LowerCoefficients]),
    maximum_absolute_value(LowerCoefficients, MaximumLower),
    Bound is 1 + MaximumLower // abs(LeadingCoefficient).

newton_monomial_terms([], _, _, _, []).
newton_monomial_terms([Coefficient|Coefficients], Order, Degree,
                      DegreeFactorial, [Term|Terms]) :-
    falling_factorial(Order, FallingFactorial),
    factorial(Order, OrderFactorial),
    Scale is DegreeFactorial // OrderFactorial,
    ScaledCoefficient is Coefficient * Scale,
    scale_polynomial(FallingFactorial, ScaledCoefficient, Term),
    NextOrder is Order + 1,
    newton_monomial_terms(Coefficients, NextOrder, Degree, DegreeFactorial,
                          Terms),
    Order =< Degree.

falling_factorial(0, [1]) :-
    !.
falling_factorial(Order, Coefficients) :-
    PreviousOrder is Order - 1,
    falling_factorial(PreviousOrder, PreviousCoefficients),
    multiply_by_x_minus(PreviousCoefficients, PreviousOrder, Coefficients).

multiply_by_x_minus([Coefficient|Coefficients], Offset,
                    [First|ProductCoefficients]) :-
    First is -Offset * Coefficient,
    multiply_by_x_minus(Coefficients, Coefficient, Offset,
                        ProductCoefficients).

multiply_by_x_minus([], LastCoefficient, _, [LastCoefficient]).
multiply_by_x_minus([Coefficient|Coefficients], PreviousCoefficient, Offset,
                    [ProductCoefficient|ProductCoefficients]) :-
    ProductCoefficient is PreviousCoefficient - Offset * Coefficient,
    multiply_by_x_minus(Coefficients, Coefficient, Offset,
                        ProductCoefficients).

scale_polynomial([], _, []).
scale_polynomial([Coefficient|Coefficients], Scale,
                 [ScaledCoefficient|ScaledCoefficients]) :-
    ScaledCoefficient is Coefficient * Scale,
    scale_polynomial(Coefficients, Scale, ScaledCoefficients).

sum_polynomials([], Sum, Sum).
sum_polynomials([Polynomial|Polynomials], Accumulator, Sum) :-
    add_polynomials(Accumulator, Polynomial, NextAccumulator),
    sum_polynomials(Polynomials, NextAccumulator, Sum).

add_polynomials([], Polynomial, Polynomial).
add_polynomials(Polynomial, [], Polynomial).
add_polynomials([Coefficient1|Coefficients1], [Coefficient2|Coefficients2],
                [Sum|Sums]) :-
    Sum is Coefficient1 + Coefficient2,
    add_polynomials(Coefficients1, Coefficients2, Sums).

factorial(0, 1) :-
    !.
factorial(Number, Factorial) :-
    PreviousNumber is Number - 1,
    factorial(PreviousNumber, PreviousFactorial),
    Factorial is Number * PreviousFactorial.

maximum_absolute_value([], 0).
maximum_absolute_value([Value|Values], Maximum) :-
    AbsoluteValue is abs(Value),
    maximum_absolute_value(Values, RemainingMaximum),
    Maximum is max(AbsoluteValue, RemainingMaximum).

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
binomial(Number, Order, 0) :-
    Order > Number,
    !.
binomial(Number, Order, Value) :-
    Order > 0,
    Order =< Number,
    PreviousOrder is Order - 1,
    binomial(Number, PreviousOrder, Previous),
    Value is Previous * (Number - Order + 1) // Order.

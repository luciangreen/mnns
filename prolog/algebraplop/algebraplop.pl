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
infer_valid_sequence(_, no_formula).

verify_affine([], _, _).
verify_affine([Value|Values], Expected, Slope) :-
    Value =:= Expected,
    Next is Expected + Slope,
    verify_affine(Values, Next, Slope).

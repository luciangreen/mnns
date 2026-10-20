:- module(mnn_s2a, [s2a/4]).

s2a(Name, Spec, Options, Result) :-
    (   \+ atom(Name)
    ->  Result = no_algorithm(invalid_name)
    ;   \+ is_list(Spec)
    ->  Result = no_algorithm(invalid_spec)
    ;   Spec = []
    ->  Result = no_algorithm(empty_spec)
    ;   \+ valid_options(Options)
    ->  Result = no_algorithm(invalid_options)
    ;   maplist(example_pair, Spec, Pairs)
    ->  (   conflicting_input(Pairs, Input)
        ->  Result = no_algorithm(conflicting_examples(Input))
        ;   unique_pairs(Pairs, UniquePairs),
            infer_result(Name, UniquePairs, Options, Result)
        )
    ;   Result = no_algorithm(unsupported_spec_shape)
    ),
    !.

valid_options(Options) :-
    is_list(Options),
    maplist(valid_option, Options),
    findall(Value, member(allow_table(Value), Options), TableOptions),
    (   TableOptions = []
    ;   TableOptions = [_]
    ).

valid_option(allow_table(true)).
valid_option(allow_table(false)).

infer_result(Name, Pairs, Options, Result) :-
    input_address_candidates(Pairs, Candidates),
    (   Candidates = [Path]
    ->  build_address_program(Name, Pairs, Path, Result)
    ;   Candidates = []
    ->  (   integer_affine(Pairs, Slope, Intercept)
        ->  build_affine_program(Name, Pairs, Slope, Intercept, Result)
        ;   integer_quadratic(Pairs, Quadratic, Linear, Constant)
        ->  build_quadratic_program(Name, Pairs, Quadratic, Linear,
                                    Constant, Result)
        ;   table_or_failure(Name, Pairs, Options, Result)
        )
    ;   memberchk(allow_table(true), Options)
    ->  build_table_program(Name, Pairs, Result)
    ;   maplist(input_address_candidate, Candidates, NamedCandidates),
        Result = no_algorithm(ambiguous(NamedCandidates))
    ).

input_address_candidates([pair(FirstInput, FirstOutput)|Pairs], Candidates) :-
    length(Pairs, RestCount),
    (   RestCount > 0
    ->  term_addresses(FirstInput, [], Addresses),
        include(valid_input_address([pair(FirstInput, FirstOutput)|Pairs]),
                Addresses, Candidates)
    ;   Candidates = []
    ).

valid_input_address(Pairs, Address) :-
    Pairs = [pair(ReferenceInput, _)|_],
    forall(member(pair(Input, Output), Pairs),
           (   term_at_address(Input, Address, Value),
               Value == Output,
               same_address_shape(ReferenceInput, Input, Address)
           )).

same_address_shape(_, _, []).
same_address_shape(Reference, Input, [Index|Address]) :-
    compound(Reference),
    compound(Input),
    functor(Reference, Functor, Arity),
    functor(Input, Functor, Arity),
    arg(Index, Reference, ReferenceArgument),
    arg(Index, Input, InputArgument),
    same_address_shape(ReferenceArgument, InputArgument, Address).

term_addresses(Term, Address, [Address|SubAddresses]) :-
    (   compound(Term)
    ->  functor(Term, _, Arity),
        findall(SubAddress,
                ( between(1, Arity, Index),
                  arg(Index, Term, Argument),
                  append(Address, [Index], ArgumentAddress),
                  term_addresses(Argument, ArgumentAddress, Addresses),
                  member(SubAddress, Addresses)
                ),
                SubAddresses)
    ;   SubAddresses = []
    ).

term_at_address(Term, [], Term).
term_at_address(Term, [Index|Address], Value) :-
    compound(Term),
    arg(Index, Term, Argument),
    term_at_address(Argument, Address, Value).

input_address_candidate(Address, input_address(Address)).

integer_affine([pair(Input0, Output0)|Pairs], Slope, Intercept) :-
    integer(Input0),
    integer(Output0),
    member(pair(Input1, Output1), Pairs),
    integer(Input1),
    integer(Output1),
    Input0 =\= Input1,
    InputDifference is Input1 - Input0,
    OutputDifference is Output1 - Output0,
    0 is OutputDifference mod InputDifference,
    Slope is OutputDifference // InputDifference,
    Intercept is Output0 - Slope * Input0,
    forall(member(pair(Input, Output), Pairs),
           ( integer(Input),
             integer(Output),
             Output =:= Slope * Input + Intercept
           )),
    !.

integer_quadratic(Pairs, Quadratic, Linear, Constant) :-
    Pairs = [pair(Input0, Output0)|Rest],
    integer(Input0),
    integer(Output0),
    member(pair(Input1, Output1), Rest),
    integer(Input1),
    integer(Output1),
    Input1 =\= Input0,
    member(pair(Input2, Output2), Rest),
    integer(Input2),
    integer(Output2),
    Input2 =\= Input0,
    Input2 =\= Input1,
    quadratic_determinants(Input0, Output0, Input1, Output1,
                          Input2, Output2,
                          Denominator, QuadraticNumerator,
                          LinearNumerator, ConstantNumerator),
    Denominator =\= 0,
    0 is QuadraticNumerator mod Denominator,
    0 is LinearNumerator mod Denominator,
    0 is ConstantNumerator mod Denominator,
    Quadratic is QuadraticNumerator // Denominator,
    Linear is LinearNumerator // Denominator,
    Constant is ConstantNumerator // Denominator,
    forall(member(pair(Input, Output), Pairs),
           ( integer(Input),
             integer(Output),
             Output =:= Quadratic * Input * Input + Linear * Input + Constant
           )),
    !.

quadratic_determinants(Input0, Output0, Input1, Output1, Input2, Output2,
                       Denominator, QuadraticNumerator,
                       LinearNumerator, ConstantNumerator) :-
    determinant3(Input0 * Input0, Input0, 1,
                 Input1 * Input1, Input1, 1,
                 Input2 * Input2, Input2, 1, Denominator),
    determinant3(Output0, Input0, 1,
                 Output1, Input1, 1,
                 Output2, Input2, 1, QuadraticNumerator),
    determinant3(Input0 * Input0, Output0, 1,
                 Input1 * Input1, Output1, 1,
                 Input2 * Input2, Output2, 1, LinearNumerator),
    determinant3(Input0 * Input0, Input0, Output0,
                 Input1 * Input1, Input1, Output1,
                 Input2 * Input2, Input2, Output2, ConstantNumerator).

determinant3(A, B, C, D, E, F, G, H, I, Determinant) :-
    Determinant is A * (E * I - F * H) -
                   B * (D * I - F * G) +
                   C * (D * H - E * G).

build_affine_program(Name, Pairs, Slope, Intercept,
                     mnn_program(
                         Module,
                         meta(s2a_affine(Name, Slope, Intercept), Events),
                         Predicates, proof([]),
                         trace([s2a_affine(
                                    Name, Slope, Intercept,
                                    examples_reproduced(Count))]))) :-
    atom_concat(mnn_s2a_, Name, Module),
    length(Pairs, Count),
    Head =.. [Name, Input, Output],
    Body = (Output is Slope * Input + Intercept),
    Events = [directive(1, module(Module, [Name/2])), clause(2)],
    Predicates = [mnn_pred(
                      Name/2, ['?', '?'], [any, any],
                      [mnn_clause(2, Head, Body,
                                  generated(s2a_affine, 2))],
                      original)].

build_quadratic_program(Name, Pairs, Quadratic, Linear, Constant,
                       mnn_program(
                           Module,
                           meta(s2a_quadratic(Name, Quadratic, Linear,
                                              Constant), Events),
                           Predicates, proof([]),
                           trace([s2a_quadratic(
                                      Name, Quadratic, Linear, Constant,
                                      examples_reproduced(Count))]))) :-
    atom_concat(mnn_s2a_, Name, Module),
    length(Pairs, Count),
    Head =.. [Name, Input, Output],
    Body = (Output is Quadratic * Input * Input + Linear * Input + Constant),
    Events = [directive(1, module(Module, [Name/2])), clause(2)],
    Predicates = [mnn_pred(
                      Name/2, ['?', '?'], [any, any],
                      [mnn_clause(2, Head, Body,
                                 generated(s2a_quadratic, 2))],
                      original)].

table_or_failure(Name, Pairs, Options, Result) :-
    (   memberchk(allow_table(true), Options)
    ->  build_table_program(Name, Pairs, Result)
    ;   Result = no_algorithm(no_generalization_candidate)
    ).

build_address_program(Name, Pairs, Address,
                      mnn_program(Module,
                                  meta(s2a_input_address(Name, Address), Events),
                                  Predicates, proof([]),
                                  trace([s2a_input_address(
                                             Name, Address,
                                             examples_reproduced(Count))]))) :-
    atom_concat(mnn_s2a_, Name, Module),
    length(Pairs, Count),
    Pairs = [pair(ExampleInput, _)|_],
    pattern_at_address(ExampleInput, Address, InputPattern, Output),
    Head =.. [Name, InputPattern, Output],
    Events = [directive(1, module(Module, [Name/2])),
              clause(2)],
    Predicates = [mnn_pred(
                      Name/2, ['?', '?'], [any, any],
                      [mnn_clause(2, Head, true,
                                  generated(s2a_input_address, 2))],
                      original)].

pattern_at_address(_, [], Variable, Variable).
pattern_at_address(Term, [Index|Address], Pattern, Value) :-
    compound(Term),
    functor(Term, Functor, Arity),
    Index >= 1,
    Index =< Arity,
    pattern_arguments(1, Arity, Index, Address, Term, Arguments, Value),
    Pattern =.. [Functor|Arguments].

pattern_arguments(Index, Arity, _, _, _, [], _) :-
    Index > Arity,
    !.
pattern_arguments(Index, Arity, SelectedIndex, Address, Term,
                  [Pattern|Patterns], Value) :-
    (   Index =:= SelectedIndex
    ->  arg(Index, Term, Selected),
        pattern_at_address(Selected, Address, Pattern, Value)
    ;   true
    ),
    NextIndex is Index + 1,
    pattern_arguments(NextIndex, Arity, SelectedIndex, Address, Term,
                      Patterns, Value).

example_pair([[input, [[InputKey, Input]]],
              [output, [[OutputKey, Output]]]],
             pair(Input, Output)) :-
    atom(InputKey),
    atom(OutputKey),
    ground(Input),
    ground(Output).

conflicting_input([pair(Input, Output)|Pairs], Input) :-
    member(pair(OtherInput, OtherOutput), Pairs),
    Input == OtherInput,
    Output \== OtherOutput,
    !.
conflicting_input([_|Pairs], Input) :-
    conflicting_input(Pairs, Input).

unique_pairs(Pairs, UniquePairs) :-
    unique_pairs(Pairs, [], UniquePairs).

unique_pairs([], _, []).
unique_pairs([pair(Input, Output)|Pairs], Seen, UniquePairs) :-
    (   member(pair(SeenInput, _), Seen),
        Input == SeenInput
    ->  unique_pairs(Pairs, Seen, UniquePairs)
    ;   UniquePairs = [pair(Input, Output)|Rest],
        unique_pairs(Pairs, [pair(Input, Output)|Seen], Rest)
    ).

build_table_program(Name, Pairs,
                    mnn_program(Module, meta(s2a_table(Name), Events), Predicates,
                                proof([]), trace([s2a_table(
                                                     Name,
                                                     examples_reproduced(Count))]))) :-
    atom_concat(mnn_s2a_, Name, Module),
    length(Pairs, Count),
    table_clauses(Name, Pairs, 2, Clauses, ClauseEvents),
    Events = [directive(1, module(Module, [Name/2]))|ClauseEvents],
    Predicates = [mnn_pred(Name/2, ['?', '?'], [any, any], Clauses, original)].

table_clauses(_, [], _, [], []).
table_clauses(Name, [pair(Input, Output)|Pairs], Id,
              [mnn_clause(Id, Head, true, generated(s2a_table, Id))|Clauses],
              [clause(Id)|Events]) :-
    Head =.. [Name, Input, Output],
    NextId is Id + 1,
    table_clauses(Name, Pairs, NextId, Clauses, Events).

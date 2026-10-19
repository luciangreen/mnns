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
    ;   \+ memberchk(allow_table(true), Options)
    ->  Result = no_algorithm(no_generalization_candidate)
    ;   maplist(example_pair, Spec, Pairs)
    ->  (   conflicting_input(Pairs, Input)
        ->  Result = no_algorithm(conflicting_examples(Input))
        ;   unique_pairs(Pairs, UniquePairs),
            build_program(Name, UniquePairs, Result)
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

build_program(Name, Pairs,
              mnn_program(Module, meta(s2a_table(Name), Events), Predicates,
                          proof([]), trace([s2a_table(Name,
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

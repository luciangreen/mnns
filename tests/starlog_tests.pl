:- begin_tests(mnn_starlog).

:- use_module('../prolog/ir/ir').
:- use_module('../prolog/starlog/starlog').

test(compiles_string_list_and_atom_concatenation) :-
    Body = conj(is(String, ':'("hello", " world")),
                conj(is(List, '&'([a], [b])),
                     is(Atom, '•'(hello, world)))),
    starlog_program(Body, Program),
    mnn_starlog:starlog_to_ir(Program, IRProgram),
    IRProgram = mnn_program(
                    _, _, [mnn_pred(example/3, _, _,
                                    [mnn_clause(_, _, Transformed, _)], _)],
                    _, _),
    Transformed = conj(string_concat("hello", " world", String),
                       conj(append([a], [b], List),
                            atom_concat(hello, world, Atom))),
    mnn_starlog:ir_to_starlog(IRProgram, RoundTripped),
    assertion(RoundTripped =@= Program).

test(compiles_declared_function_and_round_trips) :-
    Body = is(Output, twice(Input)),
    starlog_program(Body, Program),
    Program = mnn_program(Name, meta(Source, _Events), Predicates, Proof, Trace),
    Declared = mnn_program(
                   Name, meta(Source, [directive(1, starlog_function(twice/1)),
                                       clause(2)]),
                   [mnn_pred(example/2, Modes, Domains,
                             [mnn_clause(2, Head, Body, source(starlog_test, 2))],
                             original)],
                   Proof, Trace),
    Predicates = [mnn_pred(example/2, Modes, Domains,
                           [mnn_clause(1, Head, Body, source(starlog_test, 1))],
                           original)],
    mnn_starlog:starlog_to_ir(Declared, IRProgram),
    IRProgram = mnn_program(
                    _, _, [mnn_pred(example/2, _, _,
                                    [mnn_clause(_, _, twice(Input, Output), _)],
                                    _)],
                    _, _),
    mnn_starlog:ir_to_starlog(IRProgram, RoundTripped),
    assertion(RoundTripped =@= Declared).

test(compiles_declared_functions_inside_arithmetic) :-
    Body = is(Output, +(twice(Input), 1)),
    starlog_program(Body, Program),
    Program = mnn_program(Name, meta(Source, _), Predicates, Proof, Trace),
    Predicates = [mnn_pred(example/2, Modes, Domains,
                           [mnn_clause(1, Head, Body, Location)], original)],
    Declared = mnn_program(
                   Name, meta(Source, [directive(1, starlog_function(twice/1)),
                                       clause(2)]),
                   [mnn_pred(example/2, Modes, Domains,
                             [mnn_clause(2, Head, Body, Location)], original)],
                   Proof, Trace),
    mnn_starlog:starlog_to_ir(Declared, IRProgram),
    IRProgram = mnn_program(
                    _, _, [mnn_pred(example/2, _, _,
                                    [mnn_clause(_, _, Goal, _)], _)],
                    _, _),
    Goal = conj(twice(Input, Temporary), is(Output, +(Temporary, 1))).

test(compiles_declared_zero_arity_function) :-
    starlog_program(is(Output, constant), Program),
    Program = mnn_program(Name, meta(Source, _),
                          [mnn_pred(example/1, Modes, Domains,
                                    [mnn_clause(1, Head, Body, Location)],
                                    original)],
                          Proof, Trace),
    Declared = mnn_program(
                   Name, meta(Source, [directive(1, starlog_function(constant/0)),
                                       clause(2)]),
                   [mnn_pred(example/1, Modes, Domains,
                             [mnn_clause(2, Head, Body, Location)], original)],
                   Proof, Trace),
    mnn_starlog:starlog_to_ir(Declared, IRProgram),
    IRProgram = mnn_program(
                    _, _, [mnn_pred(example/1, _, _,
                                    [mnn_clause(_, _, constant(Output), _)], _)],
                    _, _),
    mnn_starlog:ir_to_starlog(IRProgram, RoundTripped),
    assertion(RoundTripped =@= Declared).

test(module_qualified_function_is_not_string_concatenation) :-
    starlog_program(is(Output, lists:reverse([1, 2])), Program),
    mnn_starlog:starlog_to_ir(Program, IRProgram),
    IRProgram = mnn_program(
                    _, _, [mnn_pred(example/1, _, _,
                                    [mnn_clause(_, _, Goal, _)], _)],
                    _, _),
    assertion(Goal =@= lists:reverse([1, 2], Output)),
    mnn_starlog:ir_to_starlog(IRProgram, RoundTripped),
    RoundTripped = mnn_program(
                       _, _, [mnn_pred(example/1, _, _,
                                       [mnn_clause(_, _, Reversed, _)], _)],
                       _, _),
    assertion(Reversed =@= is(Output, lists:reverse([1, 2]))).

test(rejects_invalid_string_operand,
     [throws(error(type_error(string, 2), _))]) :-
    starlog_program(is(_Output, ':'(2, "a")), Program),
    mnn_starlog:starlog_to_ir(Program, _).

test(rejects_invalid_atom_operand,
     [throws(error(type_error(atom, 2), _))]) :-
    starlog_program(is(_Output, '•'(hello, 2)), Program),
    mnn_starlog:starlog_to_ir(Program, _).

test(explicit_coercion_compiles_and_runs) :-
    starlog_program(is(Output, ':'(2, "a")), Program),
    mnn_starlog:starlog_to_ir(Program, [coerce(true)], IRProgram),
    IRProgram = mnn_program(
                    _, _, [mnn_pred(example/1, _, _,
                                    [mnn_clause(_, _, Goal, _)], _)],
                    _, _),
    assertion(Goal = conj(
                    mnn_starlog:coerce_text(2, Left),
                    conj(mnn_starlog:coerce_text("a", Right),
                         string_concat(Left, Right, Output)))),
    mnn_starlog:coerce_text(2, Left),
    string_concat(Left, "a", "2a").

test(rejects_undeclared_unqualified_function,
     [throws(error(existence_error(starlog_function, twice/1), _))]) :-
    starlog_program(is(_Output, twice(_Input)), Program),
    mnn_starlog:starlog_to_ir(Program, _).

test(ir_reader_parses_starlog_operators) :-
    tmp_file_stream(text, File, Stream),
    setup_call_cleanup(
        ( write(Stream,
                'result(List, Atom) :- List is [a] & [b], Atom is one • two.'),
          nl(Stream),
          close(Stream)
        ),
        ( mnn_ir:parse_program(File, Program),
          mnn_starlog:starlog_to_ir(Program, IRProgram),
          IRProgram = mnn_program(
                          _, _, [mnn_pred(result/2, _, _,
                                          [mnn_clause(_, _,
                                                      conj(append([a], [b], _List),
                                                           atom_concat(one, two,
                                                                       _Atom)),
                                                      _)], _)],
                          _, _),
          !
        ),
        delete_file(File)).

test(rejects_unknown_options,
     [throws(error(domain_error(starlog_options, [unknown]), _))]) :-
    starlog_program(true, Program),
    mnn_starlog:starlog_to_ir(Program, [unknown], _).

starlog_program(Body,
                mnn_program(starlog_test,
                            meta(source(starlog_test), [clause(1)]),
                            [mnn_pred(Key, Modes, Domains,
                                      [mnn_clause(1, Head, Body,
                                                  source(starlog_test, 1))],
                                      original)],
                            proof([]),
                            trace([]))) :-
    term_variables(Body, Variables),
    length(Variables, Arity),
    functor(Head, example, Arity),
    Head =.. [_|HeadArguments],
    HeadArguments = Variables,
    length(Modes, Arity),
    maplist(=('?'), Modes),
    length(Domains, Arity),
    maplist(=(any), Domains),
    Key = example/Arity.

:- end_tests(mnn_starlog).

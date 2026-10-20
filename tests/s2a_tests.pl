:- begin_tests(mnn_s2a).

:- use_module('../prolog/s2a/s2a').
:- use_module('../prolog/ir/ir').

test(explicit_table_emits_standalone_module_and_runs_examples) :-
    Spec = [
        [[input, [['A', [5, 6]]]], [output, [['B', [6, 5]]]]],
        [[input, [['A', [7, 8]]]], [output, [['B', [8, 7]]]]]
    ],
    mnn_s2a:s2a(table_lookup_probe, Spec, [allow_table(true)], Program),
    Program = mnn_program(mnn_s2a_table_lookup_probe,
                          meta(_, [directive(1, module(_, [table_lookup_probe/2])),
                                   clause(2), clause(3)]),
                          [mnn_pred(table_lookup_probe/2, _, _, Clauses, original)],
                          proof([]),
                          trace([s2a_table(table_lookup_probe,
                                          examples_reproduced(2))])),
    assertion(length(Clauses, 2)),
    setup_call_cleanup(
        temporary_source(File),
        ( mnn_ir:emit_program(Program, File),
          load_files(File, [silent(true)]),
          assertion(mnn_s2a_table_lookup_probe:table_lookup_probe(
                         [5, 6], [6, 5])),
          assertion(mnn_s2a_table_lookup_probe:table_lookup_probe(
                         [7, 8], [8, 7])),
          assertion(\+ mnn_s2a_table_lookup_probe:table_lookup_probe(
                          [9, 10], [10, 9])),
          assertion(\+ mnn_s2a_table_lookup_probe:table_lookup_probe(
                          unknown, unknown))
        ),
        ( unload_file(File),
          delete_file(File)
        )).

test(generalizes_a_unique_input_address_to_held_out_inputs) :-
    Spec = [
        [[input, [['A', box(red, [5, 6])]]],
         [output, [['B', [5, 6]]]]],
        [[input, [['A', box(blue, [7, 8])]]],
         [output, [['B', [7, 8]]]]]
    ],
    mnn_s2a:s2a(address_lookup_probe, Spec, [], Program),
    Program = mnn_program(
                 mnn_s2a_address_lookup_probe,
                 meta(s2a_input_address(address_lookup_probe, [2]),
                      [directive(1, module(_, [address_lookup_probe/2])),
                       clause(2)]),
                 [mnn_pred(address_lookup_probe/2, _, _, [Clause], original)],
                 proof([]),
                 trace([s2a_input_address(address_lookup_probe, [2],
                                          examples_reproduced(2))])),
    Clause = mnn_clause(2, address_lookup_probe(box(_, Output), Output), true,
                        generated(s2a_input_address, 2)),
    setup_call_cleanup(
        temporary_source(File),
        ( mnn_ir:emit_program(Program, File),
          load_files(File, [silent(true)]),
          assertion(mnn_s2a_address_lookup_probe:address_lookup_probe(
                        box(green, [9, 10]), [9, 10])),
          assertion(\+ mnn_s2a_address_lookup_probe:address_lookup_probe(
                           box(green, [9, 10]), wrong))
        ),
        ( unload_file(File),
          delete_file(File)
        )).

test(infers_integer_affine_relation_and_generalizes_held_out_inputs) :-
    Spec = [
        [[input, [['A', 1]]], [output, [['B', 5]]]],
        [[input, [['A', 2]]], [output, [['B', 7]]]],
        [[input, [['A', 4]]], [output, [['B', 11]]]]
    ],
    mnn_s2a:s2a(affine_lookup_probe, Spec, [], Program),
    Program = mnn_program(
                  mnn_s2a_affine_lookup_probe,
                  meta(s2a_affine(affine_lookup_probe, 2, 3),
                       [directive(1, module(_, [affine_lookup_probe/2])),
                        clause(2)]),
                  [mnn_pred(affine_lookup_probe/2, _, _, [Clause], original)],
                  proof([]),
                  trace([s2a_affine(affine_lookup_probe, 2, 3,
                                    examples_reproduced(3))])),
    Clause = mnn_clause(2, affine_lookup_probe(Input, Output),
                        (Output is 2 * Input + 3),
                        generated(s2a_affine, 2)),
    setup_call_cleanup(
        temporary_source(File),
        ( mnn_ir:emit_program(Program, File),
          load_files(File, [silent(true)]),
          assertion(mnn_s2a_affine_lookup_probe:affine_lookup_probe(10, 23)),
          assertion(\+ mnn_s2a_affine_lookup_probe:affine_lookup_probe(10, 24))
        ),
        ( unload_file(File),
          delete_file(File)
        )).

test(infers_constant_integer_output_from_distinct_inputs) :-
    Spec = [
        [[input, [['A', 2]]], [output, [['B', 9]]]],
        [[input, [['A', 5]]], [output, [['B', 9]]]]
    ],
    mnn_s2a:s2a(affine_lookup_probe, Spec, [],
                mnn_program(_, meta(s2a_affine(affine_lookup_probe, 0, 9), _),
                            _, _, _)).

test(rejects_nonintegral_or_inconsistent_affine_examples) :-
    NonintegralSpec = [
        [[input, [['A', 1]]], [output, [['B', 2]]]],
        [[input, [['A', 3]]], [output, [['B', 3]]]]
    ],
    InconsistentSpec = [
        [[input, [['A', 1]]], [output, [['B', 2]]]],
        [[input, [['A', 2]]], [output, [['B', 4]]]],
        [[input, [['A', 3]]], [output, [['B', 8]]]]
    ],
    mnn_s2a:s2a(affine_lookup_probe, NonintegralSpec, [],
                no_algorithm(no_generalization_candidate)),
    mnn_s2a:s2a(affine_lookup_probe, InconsistentSpec, [],
                no_algorithm(no_generalization_candidate)).

test(reports_ambiguous_input_addresses) :-
    Spec = [
        [[input, [['A', pair(red, red)]]], [output, [['B', red]]]],
        [[input, [['A', pair(blue, blue)]]], [output, [['B', blue]]]]
    ],
    mnn_s2a:s2a(address_lookup_probe, Spec, [],
                no_algorithm(ambiguous([input_address([1]),
                                        input_address([2])]))).

test(requires_matching_structure_along_an_input_address) :-
    Spec = [
        [[input, [['A', first(red, one)]]], [output, [['B', red]]]],
        [[input, [['A', second(blue, two)]]], [output, [['B', blue]]]]
    ],
    mnn_s2a:s2a(address_lookup_probe, Spec, [],
                no_algorithm(no_generalization_candidate)).

test(rejects_table_mode_without_explicit_opt_in) :-
    Spec = [[[input, [['A', one]]], [output, [['B', two]]]]],
    mnn_s2a:s2a(table_lookup_probe, Spec, [], no_algorithm(no_generalization_candidate)).

test(rejects_conflicting_outputs_for_same_input) :-
    Spec = [
        [[input, [['A', one]]], [output, [['B', first]]]],
        [[input, [['A', one]]], [output, [['B', second]]]]
    ],
    mnn_s2a:s2a(table_lookup_probe, Spec, [allow_table(true)],
                no_algorithm(conflicting_examples(one))).

test(rejects_unsupported_spec_shape) :-
    mnn_s2a:s2a(table_lookup_probe, [[input, [['A', one]]]],
                [allow_table(true)], no_algorithm(unsupported_spec_shape)).

test(rejects_empty_spec_and_invalid_options) :-
    mnn_s2a:s2a(table_lookup_probe, [], [allow_table(true)],
                no_algorithm(empty_spec)),
    mnn_s2a:s2a(table_lookup_probe,
                [[[input, [['A', one]]], [output, [['B', two]]]]],
                [unknown_option], no_algorithm(invalid_options)).

temporary_source(File) :-
    tmp_file_stream(text, File, Stream),
    close(Stream).

:- end_tests(mnn_s2a).

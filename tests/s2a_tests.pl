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

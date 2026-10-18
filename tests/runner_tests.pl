:- begin_tests(mnn_sandbox_runner).

:- use_module('../prolog/runner/sandbox_runner').

test(run_clause_program) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, [
              (pair(a, 1)),
              (pair(b, 2))
          ]),
          mnn_sandbox_runner:run_program(Source, pair(Key, Value), [],
                                         answers([[a, 1], [b, 2]]))
        ),
        delete_file(Source)).

test(run_required_builtins_and_arithmetic) :-
    source_file(run_required_builtins_and_arithmetic, TestFile),
    file_directory_name(TestFile, TestDirectory),
    directory_file_path(TestDirectory, corpus, CorpusDirectory),
    directory_file_path(CorpusDirectory, 'builtins_and_arithmetic.pl', Source),
    mnn_sandbox_runner:run_program(
        Source,
        summarize([2, 3, 5], Length, First, Last, Extended, Total, Doubled),
        [],
        answers([[3, 2, 5, [2, 3, 5, tail], 10, 20]])),
    mnn_sandbox_runner:run_program(
        Source, selected([1, 2, 3, 4, 11], Selected), [],
        answers([[2, 4]])).

test(ignore_source_directives) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, [
              (:- initialization(throw(should_not_run))),
              (value(ok))
          ]),
          mnn_sandbox_runner:run_program(Source, value(Value), [],
                                         answers([[ok]]))
        ),
        delete_file(Source)).

test(reject_unsafe_query, [throws(_)]) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, [(value(ok))]),
          mnn_sandbox_runner:run_program(Source, halt, [], _)
        ),
        delete_file(Source)).

temporary_source(File) :-
    tmp_file_stream(text, File, Stream),
    close(Stream).

write_source(File, Terms) :-
    setup_call_cleanup(
        open(File, write, Stream),
        write_source_terms(Stream, Terms),
        close(Stream)).

write_source_terms(_, []).
write_source_terms(Stream, [Term|Terms]) :-
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n'),
    write_source_terms(Stream, Terms).

:- end_tests(mnn_sandbox_runner).

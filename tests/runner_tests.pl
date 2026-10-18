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
    source_file(write_source(_, _), TestFile),
    file_directory_name(TestFile, TestDirectory),
    directory_file_path(TestDirectory, corpus, CorpusDirectory),
    directory_file_path(CorpusDirectory, 'builtins_and_arithmetic.pl', Source),
    mnn_sandbox_runner:run_program(
        Source,
        summarize([2, 3, 5], _Length, _First, _Last, _Extended, _Total,
                  _Doubled),
        [],
        answers([[3, 2, 5, [2, 3, 5, tail], 10, 20]])),
    mnn_sandbox_runner:run_program(
        Source, selected([1, 2, 3, 4, 11], _Selected), [],
        answers([[[2, 4]]])).

test(run_nth0_string_atom_and_nested_terms) :-
    corpus_source('lists_and_generators.pl', ListsAndGenerators),
    mnn_sandbox_runner:run_program(
        ListsAndGenerators, indexed_values([a, b, c], _Pairs), [],
        answers([[[0-a, 1-b, 2-c]]])),
    corpus_source('strings_and_terms.pl', StringsAndTerms),
    mnn_sandbox_runner:run_program(
        StringsAndTerms, label('sample item', _Label), [],
        answers([["hello, world"]])),
    mnn_sandbox_runner:run_program(
        StringsAndTerms, nested_term([a, b], _Term), [],
        answers([[pair(a, [b])]])).

test(run_control_flow_and_recursion) :-
    corpus_source('control_flow.pl', ControlFlow),
    mnn_sandbox_runner:run_program(
        ControlFlow, classify(2, _Positive), [], answers([[positive]])),
    mnn_sandbox_runner:run_program(
        ControlFlow, classify(0, _Zero), [], answers([[zero]])),
    mnn_sandbox_runner:run_program(
        ControlFlow, classify(-1, _Negative), [], answers([[negative]])),
    mnn_sandbox_runner:run_program(
        ControlFlow, safe_lookup([a, b], 1, _Found), [], answers([[b]])),
    mnn_sandbox_runner:run_program(
        ControlFlow, safe_lookup([a, b], invalid, _Invalid), [],
        answers([[invalid_index]])),
    corpus_source('recursive_rules.pl', RecursiveRules),
    mnn_sandbox_runner:run_program(
        RecursiveRules, ancestor(ada, _Descendant), [],
        answers([[ben], [dee], [cy]])),
    mnn_sandbox_runner:run_program(
        RecursiveRules, sum_list([1, 2, 3], _Total), [], answers([[6]])).

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

corpus_source(Name, Source) :-
    source_file(write_source(_, _), TestFile),
    file_directory_name(TestFile, TestDirectory),
    directory_file_path(TestDirectory, corpus, CorpusDirectory),
    directory_file_path(CorpusDirectory, Name, Source).

temporary_source(File) :-
    tmp_file_stream(text, File, Stream),
    close(Stream).

write_source(File, Terms) :-
    open(File, write, Stream),
    write_source_terms(Stream, Terms),
    close(Stream).

write_source_terms(_, []).
write_source_terms(Stream, [Term|Terms]) :-
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n'),
    write_source_terms(Stream, Terms).

:- end_tests(mnn_sandbox_runner).

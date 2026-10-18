:- initialization(main, main).

main :-
    prolog_load_context(directory, Directory),
    directory_file_path(Directory, 'ir_tests.pl', Tests),
    load_files(Tests, [silent(true)]),
    directory_file_path(Directory, 'test_corpus.pl', CorpusTests),
    load_files(CorpusTests, [silent(true)]),
    run_tests,
    halt.

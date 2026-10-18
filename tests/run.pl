:- initialization(main, main).

main :-
    source_file(main, RunnerFile),
    file_directory_name(RunnerFile, Directory),
    directory_file_path(Directory, 'ir_tests.pl', Tests),
    load_files(Tests, [silent(true)]),
    directory_file_path(Directory, 'test_corpus.pl', CorpusTests),
    load_files(CorpusTests, [silent(true)]),
    directory_file_path(Directory, 'runner_tests.pl', RunnerTests),
    load_files(RunnerTests, [silent(true)]),
    run_tests,
    halt.

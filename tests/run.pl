:- initialization(main, main).

main :-
    prolog_load_context(directory, Directory),
    directory_file_path(Directory, 'ir_tests.pl', Tests),
    load_files(Tests, [silent(true)]),
    run_tests,
    halt.

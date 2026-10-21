:- module(mnn_aioc_library,
          [ store_entry/2,
            get_entry/3,
            list_entries/2
          ]).

:- use_module(library(error)).
:- use_module(library(filesex)).
:- use_module('../proof/proof_checker').

store_entry(Directory, Entry) :-
    must_be(atom, Directory),
    (   valid_entry(Entry)
    ->  true
    ;   throw(error(domain_error(library_entry, Entry), _))
    ),
    Entry = mnn_library_entry(Name, Program, Original, Proof, _, _, _, _, _),
    mnn_proof_checker:check_proof(Program, Original, Proof, ProofResult),
    (   ProofResult == accepted
    ->  true
    ;   throw(error(domain_error(accepted_proof, ProofResult), _))
    ),
    make_directory_path(Directory),
    entry_file(Directory, Name, File),
    write_entry_file(File, Entry).

get_entry(Directory, Name, Result) :-
    must_be(atom, Directory),
    (   valid_name(Name)
    ->  entry_file(Directory, Name, File),
        (   exists_file(File)
        ->  read_entry_file(File, Name, Result)
        ;   Result = rejected(missing_entry)
        )
    ;   Result = rejected(invalid_name(Name))
    ).

list_entries(Directory, Names) :-
    must_be(atom, Directory),
    directory_files(Directory, Files),
    findall(Name,
            ( member(File, Files),
              atom_concat(Name, '.entry.pl', File),
              valid_name(Name)
            ),
            FoundNames),
    sort(FoundNames, Names).

valid_entry(mnn_library_entry(Name, Program, Original, Proof, Assessment,
                              Cost, Cycle, SourceForm, TestResults)) :-
    valid_name(Name),
    nonvar(Program),
    nonvar(Original),
    nonvar(Proof),
    ground(Assessment),
    ground(Cost),
    ground(Cycle),
    ground(SourceForm),
    valid_test_results(TestResults).

valid_test_results([test_result(Name, passed)|Results]) :-
    atom(Name),
    maplist(passed_test_result, Results).

passed_test_result(test_result(Name, passed)) :-
    atom(Name).

valid_name(Name) :-
    atom(Name),
    atom_chars(Name, [First|Rest]),
    name_character(First),
    maplist(name_character, Rest).

name_character(Char) :-
    char_type(Char, alnum),
    !.
name_character('_').
name_character('-').

entry_file(Directory, Name, File) :-
    atom_concat(Name, '.entry.pl', FileName),
    directory_file_path(Directory, FileName, File).

write_entry_file(File, Entry) :-
    setup_call_cleanup(
        open(File, write, Stream, [encoding(utf8), if_exists(error)]),
        (   write_term(Stream, Entry, [quoted(true), numbervars(true)]),
            write(Stream, '.\n')
        ),
        close(Stream)).

read_entry_file(File, Name, Result) :-
    setup_call_cleanup(
        open(File, read, Stream, [encoding(utf8)]),
        read_single_entry(Stream, StoredEntry),
        close(Stream)),
    (   valid_entry(StoredEntry),
        StoredEntry = mnn_library_entry(StoredName, Program, Original, Proof,
                                        _, _, _, _, _),
        StoredName == Name
    ->  mnn_proof_checker:check_proof(Program, Original, Proof, ProofResult),
        (   ProofResult == accepted
        ->  Result = accepted(StoredEntry)
        ;   Result = rejected(proof_rejected(ProofResult))
        )
    ;   Result = rejected(invalid_entry)
    ).

read_single_entry(Stream, Entry) :-
    read_term(Stream, Entry, [syntax_errors(error), module(mnn_aioc_library)]),
    (   Entry == end_of_file
    ->  throw(error(existence_error(library_entry, Stream), _))
    ;   read_term(Stream, End, [syntax_errors(error), module(mnn_aioc_library)]),
        (   End == end_of_file
        ->  true
        ;   throw(error(syntax_error(extra_library_entry_term), _))
        )
    ).

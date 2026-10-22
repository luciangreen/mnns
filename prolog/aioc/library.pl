:- module(mnn_aioc_library,
          [ store_entry/2,
            update_entry/3,
            remove_entry/3,
            get_entry/3,
            store_test_suite/3,
            get_test_suite/3,
            list_test_suites/2,
            remove_test_suite/3,
            run_entry_tests/5,
            run_and_record_entry_tests/5,
            run_entry_test_suite/5,
            run_and_record_entry_test_suite/5,
            list_entries/2,
            assess_library/2,
            rank_library/2
          ]).

:- use_module(library(error)).
:- use_module(library(filesex)).
:- use_module(library(pairs)).
:- use_module('../proof/proof_checker').
:- use_module('assessment').
:- use_module('test_runner').
:- use_module('size').

store_entry(Directory, Entry) :-
    must_be(atom, Directory),
    validate_entry(Entry),
    Entry = mnn_library_entry(Name, _, _, _, _, _, _, _, _),
    make_directory_path(Directory),
    entry_file(Directory, Name, File),
    (   exists_file(File)
    ->  throw(error(permission_error(overwrite, file, File), _))
    ;   write_entry_file(File, Entry)
    ).

update_entry(Directory, Entry, Result) :-
    must_be(atom, Directory),
    validate_entry(Entry),
    Entry = mnn_library_entry(Name, _, _, _, _, _, _, _, _),
    entry_file(Directory, Name, File),
    (   exists_file(File)
    ->  replace_entry_file(Directory, File, Entry),
        Result = updated
    ;   Result = rejected(missing_entry)
    ).

remove_entry(Directory, Name, Result) :-
    must_be(atom, Directory),
    (   valid_name(Name)
    ->  entry_file(Directory, Name, File),
        (   exists_file(File)
        ->  delete_file(File),
            Result = removed
        ;   Result = rejected(missing_entry)
        )
    ;   Result = rejected(invalid_name(Name))
    ).

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

store_test_suite(Directory, Name, TestCases) :-
    must_be(atom, Directory),
    (   valid_test_suite(Name, TestCases)
    ->  true
    ;   throw(error(domain_error(test_suite, test_suite(Name, TestCases)), _))
    ),
    make_directory_path(Directory),
    test_suite_file(Directory, Name, File),
    write_test_suite_file(File, test_suite(Name, TestCases)).

get_test_suite(Directory, Name, Result) :-
    must_be(atom, Directory),
    (   valid_name(Name)
    ->  test_suite_file(Directory, Name, File),
        (   exists_file(File)
        ->  read_test_suite_file(File, Name, Result)
        ;   Result = rejected(missing_suite)
        )
    ;   Result = rejected(invalid_name(Name))
    ).

list_test_suites(Directory, Names) :-
    must_be(atom, Directory),
    (   exists_directory(Directory)
    ->  directory_files(Directory, Files),
        findall(Name,
                ( member(File, Files),
                  atom_concat(Name, '.suite.pl', File),
                  valid_name(Name)
                ),
                FoundNames),
        sort(FoundNames, Names)
    ;   Names = []
    ).

remove_test_suite(Directory, Name, Result) :-
    must_be(atom, Directory),
    (   valid_name(Name)
    ->  test_suite_file(Directory, Name, File),
        (   exists_file(File)
        ->  delete_file(File),
            Result = removed
        ;   Result = rejected(missing_suite)
        )
    ;   Result = rejected(invalid_name(Name))
    ).

run_entry_tests(Directory, Name, TestCases, Options, Result) :-
    get_entry(Directory, Name, EntryResult),
    run_entry_tests_result(EntryResult, Name, TestCases, Options, Result).

run_entry_test_suite(Directory, EntryName, SuiteName, Options, Result) :-
    get_test_suite(Directory, SuiteName, SuiteResult),
    run_entry_test_suite_result(
        SuiteResult, Directory, EntryName, Options, Result).

run_and_record_entry_tests(Directory, Name, TestCases, Options, Result) :-
    get_entry(Directory, Name, EntryResult),
    run_and_record_entry_tests_result(
        EntryResult, Directory, Name, TestCases, Options, Result).

run_and_record_entry_test_suite(
        Directory, EntryName, SuiteName, Options, Result) :-
    get_test_suite(Directory, SuiteName, SuiteResult),
    run_and_record_entry_test_suite_result(
        SuiteResult, Directory, EntryName, Options, Result).

run_entry_test_suite_result(
        accepted(test_suite(_, TestCases)), Directory, EntryName, Options,
        Result) :-
    run_entry_tests(Directory, EntryName, TestCases, Options, Result).
run_entry_test_suite_result(
        rejected(Reason), _, EntryName, _, rejected(Reason)) :-
    valid_name(EntryName),
    !.
run_entry_test_suite_result(_, _, EntryName, _, rejected(invalid_name(EntryName))).

run_and_record_entry_test_suite_result(
        accepted(test_suite(_, TestCases)), Directory, EntryName, Options,
        Result) :-
    run_and_record_entry_tests(
        Directory, EntryName, TestCases, Options, Result).
run_and_record_entry_test_suite_result(
        rejected(Reason), _, EntryName, _, rejected(Reason)) :-
    valid_name(EntryName),
    !.
run_and_record_entry_test_suite_result(
        _, _, EntryName, _, rejected(invalid_name(EntryName))).

run_entry_tests_result(
        accepted(mnn_library_entry(Name, Candidate, Original, _, _, _, _, _, _)),
        Name, TestCases, Options, entry_test_report(Name, Results)) :-
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original, TestCases, Options, Results).
run_entry_tests_result(rejected(Reason), _, _, _, rejected(Reason)).

run_and_record_entry_tests_result(
        accepted(Entry), Directory, Name, TestCases, Options, Result) :-
    Entry = mnn_library_entry(Name, Candidate, Original, Proof, Assessment,
                              Cost, Cycle, SourceForm, _),
    mnn_aioc_test_runner:compare_programs(
        Candidate, Original, TestCases, Options, Results),
    (   Results \= [],
        maplist(passed_test_result, Results)
    ->  UpdatedEntry = mnn_library_entry(
                           Name, Candidate, Original, Proof, Assessment,
                           Cost, Cycle, SourceForm, Results),
        update_entry(Directory, UpdatedEntry, UpdateResult),
        record_status(UpdateResult, Status)
    ;   Status = not_recorded
    ),
    Result = entry_test_report(Name, Results, Status).
run_and_record_entry_tests_result(
        rejected(Reason), _, _, _, _, rejected(Reason)).

record_status(updated, recorded).
record_status(rejected(Reason), not_recorded(Reason)).

validate_entry(Entry) :-
    (   valid_entry(Entry)
    ->  true
    ;   throw(error(domain_error(library_entry, Entry), _))
    ),
    Entry = mnn_library_entry(_, Program, Original, Proof, _, _, _, _, _),
    mnn_proof_checker:check_proof(Program, Original, Proof, ProofResult),
    (   ProofResult == accepted
    ->  true
    ;   throw(error(domain_error(accepted_proof, ProofResult), _))
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

assess_library(Directory, Assessments) :-
    must_be(atom, Directory),
    list_entries(Directory, Names),
    maplist(assess_library_entry(Directory), Names, Assessments).

assess_library_entry(Directory, Name, entry_assessment(Name, Assessment)) :-
    get_entry(Directory, Name, EntryResult),
    assess_library_entry_result(EntryResult, Assessment).

assess_library_entry_result(
        accepted(mnn_library_entry(_, Candidate, Original, Proof, _, _, _, _, _)),
        Assessment) :-
    mnn_aioc_assessment:assess_candidate(
        Candidate, Original, Proof, Assessment).
assess_library_entry_result(rejected(Reason), rejected(Reason)).

rank_library(Directory, library_ranking(Ranked, Rejected)) :-
    must_be(atom, Directory),
    list_entries(Directory, Names),
    maplist(rank_library_entry(Directory), Names, Results),
    partition_ranked_entries(Results, Accepted, Rejected),
    maplist(library_entry_rank_key, Accepted, Keyed),
    keysort(Keyed, Sorted),
    pairs_values(Sorted, Ranked).

rank_library_entry(Directory, Name, Result) :-
    get_entry(Directory, Name, EntryResult),
    rank_library_entry_result(EntryResult, Name, Result).

rank_library_entry_result(
        accepted(mnn_library_entry(_, Candidate, Original, Proof, _, _, _, _, _)),
        Name,
        Result) :-
    mnn_aioc_assessment:assess_candidate(
        Candidate, Original, Proof, Assessment),
    rank_library_assessment(Name, Candidate, Assessment, Result).
rank_library_entry_result(rejected(Reason), Name, rejected_entry(Name, Reason)).

rank_library_assessment(
        Name, Candidate, assessment(accepted, Comparison),
        ranked_entry(Name, Candidate, Comparison)) :-
    !.
rank_library_assessment(Name, _, assessment(ProofResult, not_assessed),
                        rejected_entry(Name, ProofResult)).

partition_ranked_entries([], [], []).
partition_ranked_entries([ranked_entry(Name, Candidate, Comparison)|Results],
                         [ranked_entry(Name, Candidate, Comparison)|Accepted],
                         Rejected) :-
    !,
    partition_ranked_entries(Results, Accepted, Rejected).
partition_ranked_entries([rejected_entry(Name, Reason)|Results], Accepted,
                         [rejected_entry(Name, Reason)|Rejected]) :-
    partition_ranked_entries(Results, Accepted, Rejected).

library_entry_rank_key(
        ranked_entry(Name, Candidate, Comparison),
        key(WeightedTotal, Name)-ranked_entry(Name, Candidate, Comparison)) :-
    Comparison = size_comparison(_, CandidateSize, _, _),
    CandidateSize = program_size(_, _, _, _, weighted_total(WeightedTotal)).

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

valid_test_suite(Name, TestCases) :-
    valid_name(Name),
    is_list(TestCases),
    TestCases \= [],
    maplist(valid_test_case, TestCases).

valid_test_case(test_case(Name, Goal)) :-
    atom(Name),
    callable(Goal).

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

test_suite_file(Directory, Name, File) :-
    atom_concat(Name, '.suite.pl', FileName),
    directory_file_path(Directory, FileName, File).

write_test_suite_file(File, Suite) :-
    setup_call_cleanup(
        open(File, write, Stream, [encoding(utf8), if_exists(error)]),
        write_test_suite(Stream, Suite),
        close(Stream)).

write_test_suite(Stream, Suite) :-
    write_term(Stream, Suite, [quoted(true), numbervars(true)]),
    write(Stream, '.\n').

write_entry_file(File, Entry) :-
    setup_call_cleanup(
        open(File, write, Stream, [encoding(utf8), if_exists(error)]),
        write_entry(Stream, Entry),
        close(Stream)).

write_entry(Stream, Entry) :-
    write_term(Stream, Entry, [quoted(true), numbervars(true)]),
    write(Stream, '.\n').

replace_entry_file(Directory, File, Entry) :-
    temporary_entry_file(Directory, TemporaryFile),
    setup_call_cleanup(
        true,
        (   write_entry_file(TemporaryFile, Entry),
            rename_file(TemporaryFile, File)
        ),
        catch(delete_file(TemporaryFile), _, true)).

temporary_entry_file(Directory, File) :-
    tmp_file(mnn_aioc_library, UniquePath),
    file_base_name(UniquePath, UniqueName),
    atom_concat('.', UniqueName, TemporaryName0),
    atom_concat(TemporaryName0, '.tmp', TemporaryName),
    directory_file_path(Directory, TemporaryName, File).

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

read_test_suite_file(File, Name, Result) :-
    setup_call_cleanup(
        open(File, read, Stream, [encoding(utf8)]),
        read_single_entry(Stream, StoredSuite),
        close(Stream)),
    (   valid_stored_test_suite(StoredSuite),
        StoredSuite = test_suite(StoredName, TestCases),
        StoredName == Name
    ->  Result = accepted(test_suite(StoredName, TestCases))
    ;   Result = rejected(invalid_suite)
    ).

valid_stored_test_suite(test_suite(Name, TestCases)) :-
    valid_test_suite(Name, TestCases).

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

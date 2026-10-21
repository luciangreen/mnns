:- begin_tests(mnn_aioc_library).

:- use_module('../prolog/aioc/library').
:- use_module(library(filesex)).

test(stores_and_rechecks_entry_with_metadata) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, Program),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:get_entry(
              Directory, sample,
              accepted(mnn_library_entry(sample, StoredProgram, StoredOriginal,
                                         _, _, _, _, _, _))),
          assertion(StoredProgram =@= Program),
          assertion(StoredOriginal =@= Program),
          mnn_aioc_library:list_entries(Directory, [sample])
        ),
        delete_directory_and_contents(Directory)).

test(rejects_entry_without_passed_test_record) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          Entry =.. [mnn_library_entry, Name, Program, Original, Proof,
                     Assessment, Cost, Cycle, SourceForm, _],
          InvalidEntry = mnn_library_entry(
                              Name, Program, Original, Proof, Assessment, Cost,
                              Cycle, SourceForm,
                              [test_result(unit, failed)]),
          catch(mnn_aioc_library:store_entry(Directory, InvalidEntry),
                Error,
                true),
          assertion(Error = error(domain_error(library_entry, _), _)),
          assertion(Entry \== InvalidEntry)
        ),
        delete_directory_and_contents(Directory)).

test(rejects_unaccepted_proof_without_writing_entry) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          Entry =.. [mnn_library_entry, Name, Program, Original, _, Assessment,
                     Cost, Cycle, SourceForm, TestResults],
          InvalidEntry = mnn_library_entry(
                              Name, Program, Original, proof([]), Assessment,
                              Cost, Cycle, SourceForm, TestResults),
          catch(mnn_aioc_library:store_entry(Directory, InvalidEntry),
                Error,
                true),
          assertion(Error = error(domain_error(accepted_proof, _), _)),
          mnn_aioc_library:list_entries(Directory, [])
        ),
        delete_directory_and_contents(Directory)).

test(rejects_duplicate_entry_name) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          catch(mnn_aioc_library:store_entry(Directory, Entry), Error, true),
          assertion(nonvar(Error))
        ),
        delete_directory_and_contents(Directory)).

test(updates_existing_entry_after_checking_its_proof) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          updated_sample_entry(Entry, UpdatedEntry),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:update_entry(Directory, UpdatedEntry, updated),
          mnn_aioc_library:get_entry(
              Directory, sample, accepted(StoredEntry)),
          assertion(StoredEntry =@= UpdatedEntry)
        ),
        delete_directory_and_contents(Directory)).

test(rejects_update_when_entry_is_missing) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(absent, Entry, _),
          mnn_aioc_library:update_entry(
              Directory, Entry, rejected(missing_entry)),
          mnn_aioc_library:list_entries(Directory, [])
        ),
        delete_directory_and_contents(Directory)).

test(rejects_update_with_unaccepted_proof_without_changing_entry) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          Entry = mnn_library_entry(Name, Program, Original, _, Assessment,
                                    Cost, Cycle, SourceForm, TestResults),
          InvalidEntry = mnn_library_entry(
                             Name, Program, Original, proof([]), Assessment,
                             Cost, Cycle, SourceForm, TestResults),
          mnn_aioc_library:store_entry(Directory, Entry),
          catch(mnn_aioc_library:update_entry(
                    Directory, InvalidEntry, _),
                Error,
                true),
          assertion(Error = error(domain_error(accepted_proof, _), _)),
          mnn_aioc_library:get_entry(
              Directory, sample, accepted(StoredEntry)),
          assertion(StoredEntry =@= Entry)
        ),
        delete_directory_and_contents(Directory)).

test(removes_existing_entry) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:remove_entry(Directory, sample, removed),
          mnn_aioc_library:get_entry(
              Directory, sample, rejected(missing_entry)),
          mnn_aioc_library:list_entries(Directory, [])
        ),
        delete_directory_and_contents(Directory)).

test(reports_missing_entry_when_removing) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        mnn_aioc_library:remove_entry(
            Directory, absent, rejected(missing_entry)),
        delete_directory_and_contents(Directory)).

test(rejects_invalid_name_when_removing) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        mnn_aioc_library:remove_entry(
            Directory, '../outside', rejected(invalid_name('../outside'))),
        delete_directory_and_contents(Directory)).

test(rejects_path_traversal_name) :-
    sample_entry('../outside', Entry, _),
    catch(mnn_aioc_library:store_entry('/tmp', Entry), Error, true),
    assertion(Error = error(domain_error(library_entry, _), _)).

test(missing_entry_is_reported) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        mnn_aioc_library:get_entry(Directory, absent, rejected(missing_entry)),
        delete_directory_and_contents(Directory)).

test(rechecks_proof_when_reading_entry) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          directory_file_path(Directory, 'sample.entry.pl', File),
          setup_call_cleanup(
              open(File, write, Stream),
              write(Stream, 'mnn_library_entry(sample, invalid, invalid, '
                            'proof([]), recorded, cost(1), cycle(1), prolog, '
                            '[test_result(unit, passed)]).'),
              close(Stream)),
          mnn_aioc_library:get_entry(
              Directory, sample, rejected(proof_rejected(_)))
        ),
        delete_directory_and_contents(Directory)).

updated_sample_entry(
    mnn_library_entry(Name, Program, Original, Proof, _, _, _, _, _),
    mnn_library_entry(Name, Program, Original, Proof,
                      assessment(updated, recorded),
                      cost(steps(2)), cycle(2), prolog,
                      [test_result(focused_suite, passed)])).

temporary_library_directory(Directory) :-
    tmp_file(mnn_aioc_library, Directory),
    make_directory(Directory).

sample_entry(Name,
             mnn_library_entry(Name, Program, Program, Proof,
                               assessment(accepted, recorded),
                               cost(steps(1)), cycle(1), prolog,
                               [test_result(full_suite, passed)]),
             Program) :-
    Program = mnn_program(
                  library_test, meta(library_test, []),
                  [mnn_pred(answer/2, ['?', '?'], [any, any],
                            [mnn_clause(1, answer(Value, Value), true,
                                        source(library_test, 1))],
                            original)],
                  proof([]), trace([])),
    identity_proof(Proof).

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))])).

:- end_tests(mnn_aioc_library).

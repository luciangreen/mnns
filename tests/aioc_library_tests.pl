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

test(assesses_stored_entries_in_sorted_order) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(zeta, ZetaEntry, _),
          sample_entry(alpha, AlphaEntry, _),
          mnn_aioc_library:store_entry(Directory, ZetaEntry),
          mnn_aioc_library:store_entry(Directory, AlphaEntry),
          mnn_aioc_library:assess_library(
              Directory,
              [entry_assessment(alpha, AlphaAssessment),
               entry_assessment(zeta, ZetaAssessment)]),
          assert_unchanged_assessment(AlphaAssessment),
          assert_unchanged_assessment(ZetaAssessment)
        ),
        delete_directory_and_contents(Directory)).

test(ranks_proof_checked_entries_by_size_then_name) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(zeta, ZetaEntry, _),
          sample_entry(beta, BetaEntry, _),
          larger_sample_entry(alpha, AlphaEntry),
          mnn_aioc_library:store_entry(Directory, ZetaEntry),
          mnn_aioc_library:store_entry(Directory, BetaEntry),
          mnn_aioc_library:store_entry(Directory, AlphaEntry),
          mnn_aioc_library:rank_library(
              Directory,
              library_ranking(Ranked, [])),
          maplist(ranked_entry_name, Ranked, [beta, zeta, alpha]),
          Ranked = [ranked_entry(beta, _, _),
                    ranked_entry(zeta, _, _),
                    ranked_entry(alpha, _, _)],
          ranked_entry_size(Ranked, [Small, Small, Large]),
          assertion(Small < Large)
        ),
        delete_directory_and_contents(Directory)).

test(reports_entries_with_rejected_proofs_when_ranking) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(valid, ValidEntry, _),
          sample_entry(invalid, Entry, _),
          Entry = mnn_library_entry(Name, _, _, _, Assessment, Cost, Cycle,
                                    SourceForm, TestResults),
          InvalidEntry = mnn_library_entry(
                             Name, invalid, invalid, proof([]), Assessment,
                             Cost, Cycle, SourceForm, TestResults),
          mnn_aioc_library:store_entry(Directory, ValidEntry),
          mnn_aioc_library:store_entry(Directory, Entry),
          directory_file_path(Directory, 'invalid.entry.pl', File),
          setup_call_cleanup(
              open(File, write, Stream),
              ( write_term(Stream, InvalidEntry, [quoted(true)]),
                write(Stream, '.\n')
              ),
              close(Stream)),
          mnn_aioc_library:rank_library(
              Directory,
              library_ranking([ranked_entry(valid, _, _)],
                              [rejected_entry(invalid, proof_rejected(_))]))
        ),
        delete_directory_and_contents(Directory)).

test(reports_unproved_entries_in_library_assessment) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          Entry = mnn_library_entry(Name, Program, Original, _, Assessment,
                                    Cost, Cycle, SourceForm, TestResults),
          InvalidEntry = mnn_library_entry(
                             Name, Program, Original, proof([]), Assessment,
                             Cost, Cycle, SourceForm, TestResults),
          directory_file_path(Directory, 'sample.entry.pl', File),
          setup_call_cleanup(
              open(File, write, Stream),
              ( write_term(Stream, InvalidEntry, [quoted(true)]),
                write(Stream, '.\n')
              ),
              close(Stream)),
          mnn_aioc_library:assess_library(
              Directory,
              [entry_assessment(sample, rejected(proof_rejected(_)))])
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

test(runs_bounded_regression_cases_for_verified_entry) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:run_entry_tests(
              Directory, sample,
              [test_case(identity, answer(value, value))], [],
              entry_test_report(sample, [test_result(identity, passed)]))
        ),
        delete_directory_and_contents(Directory)).

test(records_test_results_only_after_every_case_passes) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:run_and_record_entry_tests(
              Directory, sample,
              [test_case(identity, answer(value, value))], [],
              entry_test_report(
                  sample, [test_result(identity, passed)], recorded)),
          mnn_aioc_library:get_entry(
              Directory, sample,
              accepted(mnn_library_entry(
                           sample, _, _, _, _, _, _, _,
                           [test_result(identity, passed)])))
        ),
        delete_directory_and_contents(Directory)).

test(does_not_record_results_when_a_case_fails) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:run_and_record_entry_tests(
              Directory, sample,
              [test_case(error, throw(error(test_failure, _)))], [],
              entry_test_report(
                  sample, [test_result(error, failed(candidate_error(_)))],
                  not_recorded)),
          mnn_aioc_library:get_entry(
              Directory, sample,
              accepted(mnn_library_entry(
                           sample, _, _, _, _, _, _, _,
                           [test_result(full_suite, passed)])))
        ),
        delete_directory_and_contents(Directory)).

test(does_not_record_inconclusive_test_results) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:run_and_record_entry_tests(
              Directory, sample, [test_case(members, member(_, [a, b]))],
              [max_answers(1)],
              entry_test_report(
                  sample,
                  [test_result(members, inconclusive(answer_limit_exceeded(1)))],
                  not_recorded)),
          mnn_aioc_library:get_entry(
              Directory, sample,
              accepted(mnn_library_entry(
                           sample, _, _, _, _, _, _, _,
                           [test_result(full_suite, passed)])))
        ),
        delete_directory_and_contents(Directory)).

test(reports_missing_entry_when_running_tests) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        mnn_aioc_library:run_entry_tests(
            Directory, absent, [], [], rejected(missing_entry)),
        delete_directory_and_contents(Directory)).

test(rechecks_stored_proof_before_running_tests) :-
    temporary_library_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_entry(sample, Entry, _),
          Entry = mnn_library_entry(Name, _, _, _, Assessment, Cost, Cycle,
                                    SourceForm, TestResults),
          InvalidEntry = mnn_library_entry(
                             Name, invalid, invalid, proof([]), Assessment,
                             Cost, Cycle, SourceForm, TestResults),
          directory_file_path(Directory, 'sample.entry.pl', File),
          setup_call_cleanup(
              open(File, write, Stream),
              ( write_term(Stream, InvalidEntry, [quoted(true)]),
                write(Stream, '.\n')
              ),
              close(Stream)),
          mnn_aioc_library:run_entry_tests(
              Directory, sample,
              [test_case(unsafe, throw(error(test_failure, _)))], [],
              rejected(proof_rejected(_)))
        ),
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
              ( Entry = mnn_library_entry(Name, _, _, _, Assessment, Cost,
                                          Cycle, SourceForm, TestResults),
                InvalidEntry = mnn_library_entry(
                                   Name, invalid, invalid, proof([]),
                                   Assessment, Cost, Cycle, SourceForm,
                                   TestResults),
                write_term(Stream, InvalidEntry, [quoted(true)]),
                write(Stream, '.\n')
              ),
              close(Stream)),
          mnn_aioc_library:get_entry(
              Directory, sample, rejected(proof_rejected(_)))
        ),
        delete_directory_and_contents(Directory)).

assert_unchanged_assessment(
    assessment(
        accepted,
        size_comparison(_, _, weighted_delta(0), structural_effect(unchanged)))).

ranked_entry_name(ranked_entry(Name, _, _), Name).

ranked_entry_size(Ranked, Sizes) :-
    maplist(ranked_entry_weighted_size, Ranked, Sizes).

ranked_entry_weighted_size(
    ranked_entry(_, _, size_comparison(_, CandidateSize, _, _)),
    WeightedTotal) :-
    CandidateSize = program_size(_, _, _, _, weighted_total(WeightedTotal)).

updated_sample_entry(
    mnn_library_entry(Name, Program, Original, Proof, _, _, _, _, _),
    mnn_library_entry(Name, Program, Original, Proof,
                      assessment(updated, recorded),
                      cost(steps(2)), cycle(2), prolog,
                      [test_result(focused_suite, passed)])).

larger_sample_entry(Name, Entry) :-
    sample_entry(Name, Entry0, Program0),
    Program0 = mnn_program(ProgramName, Meta, Predicates, Proof, Trace),
    append(Predicates,
           [mnn_pred(extra/0, [], [],
                     [mnn_clause(2, extra, true, source(ProgramName, 2))],
                     original)],
           LargerPredicates),
    Program = mnn_program(ProgramName, Meta, LargerPredicates, Proof, Trace),
    Entry0 = mnn_library_entry(Name, _, _, EntryProof, Assessment, Cost, Cycle,
                              SourceForm, TestResults),
    Entry = mnn_library_entry(Name, Program, Program, EntryProof, Assessment,
                             Cost, Cycle, SourceForm, TestResults).

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
                  library_test, meta(library_test, [clause(1)]),
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

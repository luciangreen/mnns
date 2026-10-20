:- begin_tests(mnn_aioc_bundle).

:- use_module('../prolog/aioc/bundle').
:- use_module(library(filesex)).

test(writes_and_rechecks_complete_bundle) :-
    temporary_bundle_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_program(Program, Proof),
          mnn_aioc_bundle:write_bundle(
              mnn_bundle(Program, Program, Proof, trace([]),
                         "# Bundle report\n"),
              Directory,
              sample),
          forall(member(Suffix,
                        ['.pl', '.original.pl', '.proof.pl', '.proof.md',
                         '.trace.pl', '.report.md']),
                 ( atom_concat(sample, Suffix, FileName),
                   directory_file_path(Directory, FileName, File),
                   assertion(exists_file(File))
                 )),
          mnn_aioc_bundle:check_bundle(Directory, sample, accepted)
        ),
        delete_directory_and_contents(Directory)).

test(rejects_unaccepted_proof_without_writing_bundle) :-
    temporary_bundle_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_program(Program, _),
          catch(mnn_aioc_bundle:write_bundle(
                    mnn_bundle(Program, Program, proof([]), trace([]), ""),
                    Directory, rejected),
                Error,
                true),
          assertion(nonvar(Error)),
          assertion(Error = error(domain_error(accepted_proof, _), _)),
          directory_file_path(Directory, 'rejected.pl', ProgramFile),
          assertion(\+ exists_file(ProgramFile))
        ),
        delete_directory_and_contents(Directory)).

test(rejects_modified_program_source, [nondet]) :-
    temporary_bundle_directory(Directory),
    setup_call_cleanup(
        true,
        ( sample_program(Program, Proof),
          mnn_aioc_bundle:write_bundle(
              mnn_bundle(Program, Program, Proof, trace([]), ""),
              Directory, sample),
          directory_file_path(Directory, 'sample.pl', ProgramFile),
          setup_call_cleanup(
              open(ProgramFile, write, Stream),
              write(Stream, 'other_program.'),
              close(Stream)),
          mnn_aioc_bundle:check_bundle(
              Directory, sample, rejected(bundle_program_mismatch))
        ),
        delete_directory_and_contents(Directory)).

test(rejects_bundle_names_that_escape_directory) :-
    sample_program(Program, Proof),
    catch(mnn_aioc_bundle:write_bundle(
              mnn_bundle(Program, Program, Proof, trace([]), ""),
              '/tmp', '../outside'),
          Error,
          true),
    assertion(nonvar(Error)),
    assertion(Error = error(domain_error(bundle_name, '../outside'), _)).

test(bundle_check_reads_program_directives_as_data) :-
    temporary_bundle_directory(Directory),
    setup_call_cleanup(
        true,
        ( Program = mnn_program(
                        bundle_directive,
                        meta(bundle_directive,
                             [directive(
                                  1,
                                  initialization(assertz(user:bundle_marker)))]),
                        [], proof([]), trace([])),
          identity_proof(Proof),
          mnn_aioc_bundle:write_bundle(
              mnn_bundle(Program, Program, Proof, trace([]), ""),
              Directory, directive),
          mnn_aioc_bundle:check_bundle(Directory, directive, accepted),
          assertion(\+ current_predicate(user:bundle_marker/0))
        ),
        delete_directory_and_contents(Directory)).

temporary_bundle_directory(Directory) :-
    tmp_file(mnn_bundle, Directory),
    make_directory(Directory).

sample_program(Program, Proof) :-
    Program = mnn_program(
                  sample, meta(sample, []),
                  [mnn_pred(answer/1, ['?'], [any],
                            [mnn_clause(1, answer(ok), true,
                                        source(sample, 1))],
                            original)],
                  proof([]), trace([])),
    identity_proof(Proof).

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(bundle_test), modes([])))])).

:- end_tests(mnn_aioc_bundle).

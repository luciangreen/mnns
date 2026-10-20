:- module(mnn_aioc_bundle,
          [ write_bundle/3,
            check_bundle/3
          ]).

:- use_module(library(error)).
:- use_module(library(filesex)).
:- use_module('../ir/ir').
:- use_module('../proof/proof_checker').
:- use_module('../proof/proof_renderer').

write_bundle(mnn_bundle(Program, Original, Proof, Trace, Report),
             Directory,
             Name) :-
    must_be(atom, Directory),
    valid_bundle_name(Name),
    must_be(ground, Trace),
    must_be(string, Report),
    mnn_proof_checker:check_proof(Program, Original, Proof, Result),
    (   Result == accepted
    ->  true
    ;   throw(error(domain_error(accepted_proof, Result), _))
    ),
    make_directory_path(Directory),
    bundle_paths(Directory, Name, Paths),
    Paths = bundle_paths(ProgramFile, OriginalFile, ProofFile, ProofMarkdown,
                         TraceFile, ReportFile),
    mnn_ir:emit_program(Program, ProgramFile),
    mnn_ir:emit_program(Original, OriginalFile),
    write_term_file(ProofFile, bundle_proof(Program, Original, Proof)),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    write_text_file(ProofMarkdown, Markdown),
    write_term_file(TraceFile, Trace),
    write_text_file(ReportFile, Report).

check_bundle(Directory, Name, Result) :-
    must_be(atom, Directory),
    valid_bundle_name(Name),
    bundle_paths(Directory, Name, Paths),
    Paths = bundle_paths(ProgramFile, OriginalFile, ProofFile, ProofMarkdown,
                         TraceFile, ReportFile),
    (   missing_bundle_file(Paths, Missing)
    ->  Result = rejected(missing_bundle_file(Missing))
    ;   mnn_ir:parse_program(ProgramFile, EmittedProgram),
        mnn_ir:parse_program(OriginalFile, EmittedOriginal),
        read_single_term(ProofFile, StoredProof),
        check_stored_bundle(StoredProof, EmittedProgram, EmittedOriginal,
                            Result)
    ).

check_stored_bundle(bundle_proof(Program, Original, Proof),
                    EmittedProgram, EmittedOriginal, Result) :-
    !,
    (   same_emitted_program(Program, EmittedProgram),
        same_emitted_program(Original, EmittedOriginal)
    ->  mnn_proof_checker:check_proof(Program, Original, Proof, Result)
    ;   Result = rejected(bundle_program_mismatch)
    ).
check_stored_bundle(_, _, _, rejected(invalid_bundle_proof)).

same_emitted_program(Program, EmittedProgram) :-
    mnn_ir:ir_to_prolog(Program, ProgramTerms),
    mnn_ir:ir_to_prolog(EmittedProgram, EmittedTerms),
    ProgramTerms =@= EmittedTerms.

missing_bundle_file(Paths, Missing) :-
    Paths = bundle_paths(_, _, _, _, _, _),
    Paths =.. [_|Files],
    member(Missing, Files),
    \+ exists_file(Missing),
    !.

bundle_paths(Directory, Name,
             bundle_paths(ProgramFile, OriginalFile, ProofFile, ProofMarkdown,
                          TraceFile, ReportFile)) :-
    bundle_path(Directory, Name, '.pl', ProgramFile),
    bundle_path(Directory, Name, '.original.pl', OriginalFile),
    bundle_path(Directory, Name, '.proof.pl', ProofFile),
    bundle_path(Directory, Name, '.proof.md', ProofMarkdown),
    bundle_path(Directory, Name, '.trace.pl', TraceFile),
    bundle_path(Directory, Name, '.report.md', ReportFile).

bundle_path(Directory, Name, Suffix, Path) :-
    atom_concat(Name, Suffix, FileName),
    directory_file_path(Directory, FileName, Path).

valid_bundle_name(Name) :-
    (   atom(Name),
        atom_chars(Name, [First|Rest]),
        bundle_name_char(First),
        maplist(bundle_name_char, Rest)
    ->  true
    ;   throw(error(domain_error(bundle_name, Name), _))
    ).

bundle_name_char(Char) :-
    char_type(Char, alnum),
    !.
bundle_name_char('_').
bundle_name_char('-').

write_term_file(File, Term) :-
    setup_call_cleanup(
        open(File, write, Stream, [encoding(utf8)]),
        (   write_term(Stream, Term, [quoted(true), numbervars(true)]),
            write(Stream, '.\n')
        ),
        close(Stream)).

write_text_file(File, Text) :-
    setup_call_cleanup(
        open(File, write, Stream, [encoding(utf8)]),
        format(Stream, '~s', [Text]),
        close(Stream)).

read_single_term(File, Term) :-
    setup_call_cleanup(
        open(File, read, Stream, [encoding(utf8)]),
        read_single_term_from_stream(Stream, Term),
        close(Stream)).

read_single_term_from_stream(Stream, Term) :-
    read_term(Stream, Term, [syntax_errors(error), module(mnn_aioc_bundle)]),
    (   Term == end_of_file
    ->  throw(error(existence_error(bundle_proof, Stream), _))
    ;   read_term(Stream, End, [syntax_errors(error), module(mnn_aioc_bundle)]),
        (   End == end_of_file
        ->  true
        ;   throw(error(domain_error(single_term_bundle_proof, FileTerm),
                        _))
        )
    ).

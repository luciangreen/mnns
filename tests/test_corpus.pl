:- begin_tests(mnn_ir_corpus).

:- use_module('../prolog/ir/ir').

test(round_trip_corpus) :-
    corpus_programs(Files),
    assertion(Files \= []),
    maplist(round_trip_file, Files).

corpus_programs(Files) :-
    source_file(round_trip_file(_), TestFile),
    file_directory_name(TestFile, TestDirectory),
    directory_file_path(TestDirectory, corpus, CorpusDirectory),
    directory_files(CorpusDirectory, Entries),
    include(prolog_file, Entries, Names),
    maplist(file_in_directory(CorpusDirectory), Names, Files).

prolog_file(Name) :-
    file_name_extension(_, pl, Name),
    \+ sub_atom(Name, 0, 1, _, '.').

file_in_directory(Directory, Name, File) :-
    directory_file_path(Directory, Name, File).

round_trip_file(Source) :-
    mnn_ir:parse_program(Source, Program),
    mnn_ir:ir_to_prolog(Program, Terms),
    setup_call_cleanup(
        tmp_file_stream(text, Emitted, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Emitted),
          mnn_ir:parse_program(Emitted, Reparsed),
          compare_programs(Program, Reparsed, Terms)
        ),
        ( catch(close(Stream), _, true),
          delete_file(Emitted)
        )).

compare_programs(mnn_program(_, meta(_, Events), Predicates, _, _),
                 mnn_program(_, meta(_, ReparsedEvents), ReparsedPredicates, _, _),
                 Terms) :-
    assertion(Terms \= []),
    assertion(Events =@= ReparsedEvents),
    canonical_predicates(Predicates, Canonical),
    canonical_predicates(ReparsedPredicates, ReparsedCanonical),
    assertion(Canonical =@= ReparsedCanonical).

canonical_predicates([], []).
canonical_predicates(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    [mnn_pred(Key, Modes, Domains, CanonicalClauses, Status)|Rest]) :-
    canonical_clauses(Clauses, CanonicalClauses),
    canonical_predicates(Predicates, Rest).

canonical_clauses([], []).
canonical_clauses([mnn_clause(Id, Head, Body, _)|Clauses],
                  [mnn_clause(Id, Head, Body)|Rest]) :-
    canonical_clauses(Clauses, Rest).

:- end_tests(mnn_ir_corpus).

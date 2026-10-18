:- begin_tests(mnn_ir).

:- use_module('../prolog/ir/ir').

test(parse_and_emit_round_trip) :-
    temporary_source(Source),
    write_source(Source, [
        (:- module(sample, [result/2])),
        (result(X, Y) :- (integer(X), Y is X + 1 ; Y = X)),
        result(0, zero),
        (choose(X, Y) :- (X > 0 -> Y = positive ; Y = nonpositive)),
        (guarded(X) :- \+ integer(X))
    ]),
    mnn_ir:parse_program(Source, Program),
    Program = mnn_program(sample, _, Predicates, proof([]), trace([])),
    assertion(Predicates = [
        mnn_pred(result/2, ['?', '?'], [any, any],
                 [mnn_clause(2, _, disj(conj(_, _), _), _),
                  mnn_clause(3, _, true, _)], original),
        mnn_pred(choose/2, ['?', '?'], [any, any],
                 [mnn_clause(4, _, ite(_, _, _), _)], original),
        mnn_pred(guarded/1, ['?'], [any],
                 [mnn_clause(5, _, not(_), _)], original)
    ]),
    mnn_ir:ir_to_prolog(Program, Terms),
    temporary_source(Emitted),
    assertion(length(Terms, 5)),
    mnn_ir:emit_program(Program, Emitted),
    mnn_ir:parse_program(Emitted, Reparsed),
    Reparsed = mnn_program(sample, _, ReparsedPredicates, proof([]), trace([])),
    canonical_predicates(Predicates, Canonical),
    canonical_predicates(ReparsedPredicates, ReparsedCanonical),
    assertion(Canonical =@= ReparsedCanonical),
    delete_file(Source),
    delete_file(Emitted).

test(reject_call_goal, [throws(error(domain_error(call_free_goal, _), _))]) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, [(unsafe :- call(true))]),
          mnn_ir:parse_program(Source, _)
        ),
        delete_file(Source)).

test(normalizes_and_emits_once_goal) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source,
                       [(once_example(X) :-
                             once((X = first ; X = second)))]),
          mnn_ir:parse_program(Source, Program),
          Program = mnn_program(_, _, Predicates, _, _),
          assertion(Predicates = [
              mnn_pred(once_example/1, ['?'], [any],
                       [mnn_clause(_, _,
                                   once(disj(First = first, Second = second)),
                                   _)],
                       original)
          ]),
          assertion(First == Second),
          setup_call_cleanup(
              temporary_source(Emitted),
              ( mnn_ir:emit_program(Program, Emitted),
                mnn_ir:parse_program(Emitted, Reparsed),
                Reparsed = mnn_program(_, _, ReparsedPredicates, _, _),
                assertion(Predicates =@= ReparsedPredicates)
              ),
              delete_file(Emitted))
        ),
        delete_file(Source)).

test(reject_call_with_extra_arguments,
     [throws(error(domain_error(call_free_goal, _), _))]) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, [(unsafe(Goal) :- call(Goal, extra))]),
          mnn_ir:parse_program(Source, _)
        ),
        delete_file(Source)).

test(preserves_clause_source_lines) :-
    setup_call_cleanup(
        temporary_source(Source),
        ( write_source(Source, [
              (:- module(located, [])),
              first_fact,
              (second_rule :- true)
          ]),
          mnn_ir:parse_program(Source, mnn_program(_, _, Predicates, _, _)),
          assertion(Predicates = [
              mnn_pred(first_fact/0, [], [], [mnn_clause(2, _, true,
                                                        source(Source, 2))], original),
              mnn_pred(second_rule/0, [], [], [mnn_clause(3, _, true,
                                                          source(Source, 3))], original)
          ])
        ),
        delete_file(Source)).

temporary_source(File) :-
    tmp_file_stream(text, File, Stream),
    close(Stream).

write_source(File, Terms) :-
    open(File, write, Stream),
    write_source_terms(Stream, Terms),
    close(Stream).

write_source_terms(_, []).
write_source_terms(Stream, [Term|Terms]) :-
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n'),
    write_source_terms(Stream, Terms).

canonical_predicates([], []).
canonical_predicates([mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
                     [mnn_pred(Key, Modes, Domains, CanonicalClauses, Status)|Rest]) :-
    canonical_clauses(Clauses, CanonicalClauses),
    canonical_predicates(Predicates, Rest).

canonical_clauses([], []).
canonical_clauses([mnn_clause(Id, Head, Body, _)|Clauses],
                  [mnn_clause(Id, Head, Body)|Rest]) :-
    canonical_clauses(Clauses, Rest).

:- end_tests(mnn_ir).

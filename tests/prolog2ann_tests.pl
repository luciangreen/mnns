:- begin_tests(prolog2ann).

:- use_module('../prolog/prolog2ann/parse').
:- use_module('../prolog/prolog2ann/normalise').

test(parse_source_and_optional_domain) :-
    with_temp_file("parent(ann, bob).\nancestor(X, Y) :- parent(X, Y).\n",
                   Source,
                   with_temp_file(
                       "domain(person, [ann, bob]).\nrange(n, 0, 20).\n",
                       Domain,
                       (   prolog2ann_parse:parse_file(
                               Source, Domain,
                               ann_source(Source, Clauses, Domains)),
                           Clauses = [ann_clause(1, parent(ann, bob), true,
                                                 [], Source, 1),
                                      ann_clause(2, ancestor(A, B),
                                                 parent(C, D),
                                                 Names, Source, 2)],
                           Names = [NameA=VarA, NameB=VarB],
                           NameA == 'X',
                           NameB == 'Y',
                           A == VarA,
                           B == VarB,
                           C == VarA,
                           D == VarB,
                           Domains = [domain(person, [ann, bob]),
                                      range(n, 0, 20)]
                       ))).

test(normalize_disjunction_and_conjunction) :-
    Source = ann_source(
                source,
                [ann_clause(1, answer(X), (left(X) ; right(X), extra(X)),
                            [X=_], source, 1)],
                []),
    once(prolog2ann_normalise:normalize_program(
             Source,
             ann_program(source,
                         [ann_clause(1-1, answer(_), [left(_)], [_=_],
                                    source, 1),
                          ann_clause(1-2, answer(_), [right(_), extra(_)],
                                     [_=_], source, 1)],
                         []))).

test(arithmetic_goals_moved_to_end) :-
    Source = ann_source(
                source,
                [ann_clause(1, result(X), (source_value(Y), X is Y + 1, X < 4),
                            [X=_, Y=_], source, 1)],
                []),
    once(prolog2ann_normalise:normalize_program(
             Source,
             ann_program(source,
                         [ann_clause(1-1, result(X),
                                     [source_value(Y), X is Y + 1, X < 4],
                                     _, source, 1)],
                         []))).

test(stratified_negation_accepted) :-
    Source = ann_source(
                source,
                [ann_clause(1, allowed(X), (person(X), \+ blocked(X)),
                            [X=_], source, 1),
                 ann_clause(2, blocked(bob), true, [], source, 2),
                 ann_clause(3, person(ann), true, [], source, 3)],
                []),
    once(prolog2ann_normalise:normalize_program(
             Source,
             ann_program(source, [_, _, _], []))).

test(non_stratified_negation_reports_cycle) :-
    Clauses =
        [ann_clause(1, p(X), [not(q(X))], [X=_], source, 1),
         ann_clause(2, q(X), [p(X)], [X=_], source, 2)],
    catch(prolog2ann_normalise:check_stratification(Clauses),
          error(non_stratified_negation(Cycle), file(source, 1)),
          true),
    Cycle == [p/1, q/1, p/1].

test(cut_rejected_with_source_location,
     [throws(error(unsupported_construct(!), file(_, 2)))]) :-
    with_temp_file("ok.\nanswer :- !.\n", Source,
                   prolog2ann_parse:parse_file(Source, none, _)).

test(findall_rejected_with_source_location,
     [throws(error(unsupported_construct(findall/3), file(_, 1)))]) :-
    with_temp_file("answers(X) :- findall(Y, item(Y), X).\n", Source,
                   prolog2ann_parse:parse_file(Source, none, _)).

with_temp_file(Content, File, Goal) :-
    setup_call_cleanup(
        tmp_file_stream(text, File, Stream),
        (   format(Stream, '~s', [Content]),
            close(Stream),
            call(Goal)
        ),
        (   catch(close(Stream), _, true),
            catch(delete_file(File), _, true)
        )).

:- end_tests(prolog2ann).

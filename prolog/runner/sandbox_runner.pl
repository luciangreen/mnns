:- module(mnn_sandbox_runner,
          [ run_program/4
          ]).

:- use_module('../ir/ir').
:- use_module(library(option)).
:- use_module(library(sandbox)).
:- use_module(library(solution_sequences)).
:- use_module(library(time)).

run_program(File, Goal, Options, answers(Answers)) :-
    validate_options(Options, MaxAnswers, TimeLimit),
    (   callable(Goal)
    ->  true
    ;   throw(error(type_error(callable, Goal), _))
    ),
    mnn_ir:parse_program(File, Program),
    mnn_ir:ir_to_prolog(Program, Terms),
    clause_terms(Program, Terms, Clauses),
    maplist(validate_clause_head, Clauses),
    with_mutex(mnn_sandbox_runner,
               once(run_isolated(Clauses, Goal, MaxAnswers, TimeLimit,
                                 Answers))).

validate_options(Options, MaxAnswers, TimeLimit) :-
    (   is_list(Options)
    ->  true
    ;   throw(error(type_error(list, Options), _))
    ),
    maplist(known_option, Options),
    option(max_answers(MaxAnswers), Options, 100),
    option(time_limit(TimeLimit), Options, 5),
    (   integer(MaxAnswers),
        MaxAnswers > 0
    ->  true
    ;   throw(error(domain_error(positive_integer, MaxAnswers), _))
    ),
    (   number(TimeLimit),
        TimeLimit > 0
    ->  true
    ;   throw(error(domain_error(positive_number, TimeLimit), _))
    ).

known_option(max_answers(_)).
known_option(time_limit(_)).

clause_terms(mnn_program(_, meta(_, Events), _, _, _), Terms, Clauses) :-
    clause_terms_by_event(Events, Terms, Clauses).

clause_terms_by_event([], [], []).
clause_terms_by_event([directive(_, _)|Events], [_|Terms], Clauses) :-
    clause_terms_by_event(Events, Terms, Clauses).
clause_terms_by_event([clause(_)|Events], [Term|Terms], [Term|Clauses]) :-
    clause_terms_by_event(Events, Terms, Clauses).

validate_clause_head((Head :- _)) :-
    !,
    validate_clause_head(Head).
validate_clause_head(Head) :-
    (   nonvar(Head),
        Head = (_:_)
    ->  throw(error(permission_error(define, qualified_predicate, Head), _))
    ;   true
    ).

run_isolated(Clauses, Goal, MaxAnswers, TimeLimit, Answers) :-
    term_variables(Goal, Variables),
    setup_call_cleanup(
        tmp_file_stream(text, File, Stream),
        ( file_name_extension(File, pl, SourceFile),
          file_base_name(SourceFile, SourceFileName),
          file_name_extension(SourceBase, pl, SourceFileName),
          atom_concat(mnn_sandbox_runner_program_, SourceBase, ProgramModule),
          write_terms(
              Stream,
              [(:- module(ProgramModule, []))|Clauses]),
          close(Stream),
          rename_file(File, SourceFile),
          load_files(SourceFile,
                     [module(ProgramModule), silent(true)]),
          setup_call_cleanup(
              sandbox:safe_goal(ProgramModule:Goal),
              call_with_time_limit(
                  TimeLimit,
                  findnsols(MaxAnswers, Variables,
                            ProgramModule:Goal, Answers)),
              unload_file(SourceFile))
        ),
        ( catch(close(Stream), _, true),
          catch(unload_file(SourceFile), _, true),
          catch(delete_file(SourceFile), _, true),
          catch(delete_file(File), _, true)
        )).

write_terms(_, []) :-
    !.
write_terms(Stream, [Term|Terms]) :-
    !,
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n\n'),
    write_terms(Stream, Terms).

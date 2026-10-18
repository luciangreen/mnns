:- module(mnn_ir,
          [ parse_program/2,
            ir_to_prolog/2,
            emit_program/2
          ]).

:- use_module(library(lists)).

parse_program(File, Program) :-
    setup_call_cleanup(
        open(File, read, Stream),
        read_terms(Stream, File, 1, Terms),
        close(Stream)),
    number_terms(Terms, 1, NumberedTerms),
    build_program(File, NumberedTerms, Program).

read_terms(Stream, File, Id, Terms) :-
    stream_property(Stream, position(Position)),
    stream_position_data(line_count, Position, Line),
    read_term(Stream, Term, [syntax_errors(error), module(mnn_ir)]),
    (   Term == end_of_file
    ->  Terms = []
    ;   SourceLine is Line + 1,
        Terms = [located(Id, SourceLine, Term)|Rest],
        NextId is Id + 1,
        read_terms(Stream, File, NextId, Rest)
    ).

number_terms([], _, []).
number_terms([located(Id, Line, Term)|Terms], NextId, Numbered) :-
    (   Term = (:- Directive)
    ->  Numbered = [directive(Id, Directive)|Rest]
    ;   Term = (Head :- Body)
    ->  (   callable(Head)
        ->  true
        ;   throw(error(domain_error(callable_head, Head), _))
        ),
        check_goal(Body),
        Numbered = [clause(Id, Head, Body, Line)|Rest]
    ;   callable(Term)
    ->  Numbered = [clause(Id, Term, true, Line)|Rest]
    ;   throw(error(domain_error(prolog_program_term, Term), _))
    ),
    Next is NextId + 1,
    number_terms(Terms, Next, Rest).

build_program(File, Terms, mnn_program(Name, Meta, Predicates, proof([]), trace([]))) :-
    program_name(Terms, File, Name),
    collect_predicates(Terms, File, [], Predicates),
    collect_events(Terms, Events),
    Meta = meta(File, Events).

program_name(Terms, _, Name) :-
    member(directive(_, module(Name, _)), Terms),
    !.
program_name(Terms, _, Name) :-
    member(directive(_, module(Name)), Terms),
    !.
program_name(_, File, Name) :-
    file_base_name(File, BaseName),
    file_name_extension(Name, _, BaseName).

collect_predicates([], _, Predicates, Predicates).
collect_predicates([clause(Id, Head, Body, Line)|Terms], File, Acc, Predicates) :-
    functor(Head, Name, Arity),
    source_body(Body, NormalizedBody),
    Clause = mnn_clause(Id, Head, NormalizedBody, source(File, Line)),
    add_clause(Name/Arity, Clause, Acc, Next),
    collect_predicates(Terms, File, Next, Predicates).
collect_predicates([directive(_, _)|Terms], File, Acc, Predicates) :-
    collect_predicates(Terms, File, Acc, Predicates).

add_clause(Name/Arity, Clause, [], [mnn_pred(Name/Arity, Modes, Domains, [Clause], original)]) :-
    unknown_modes(Arity, Modes),
    unknown_domains(Arity, Domains).
add_clause(Name/Arity, Clause,
           [mnn_pred(Name/Arity, Modes, Domains, Clauses, Status)|Predicates],
           [mnn_pred(Name/Arity, Modes, Domains, UpdatedClauses, Status)|Predicates]) :-
    !,
    append(Clauses, [Clause], UpdatedClauses).
add_clause(Key, Clause, [Predicate|Predicates], [Predicate|Next]) :-
    add_clause(Key, Clause, Predicates, Next).

unknown_modes(0, []) :-
    !.
unknown_modes(Arity, ['?'|Modes]) :-
    Arity > 0,
    Remaining is Arity - 1,
    unknown_modes(Remaining, Modes).

unknown_domains(0, []) :-
    !.
unknown_domains(Arity, [any|Domains]) :-
    Arity > 0,
    Remaining is Arity - 1,
    unknown_domains(Remaining, Domains).

collect_events([], []).
collect_events([directive(Id, Directive)|Terms], [directive(Id, Directive)|Events]) :-
    collect_events(Terms, Events).
collect_events([clause(Id, _, _, _)|Terms], [clause(Id)|Events]) :-
    collect_events(Terms, Events).

source_body((If -> Then ; Else), ite(NormalizedIf, NormalizedThen, NormalizedElse)) :-
    !,
    source_body(If, NormalizedIf),
    source_body(Then, NormalizedThen),
    source_body(Else, NormalizedElse).
source_body((If -> Then), ite(NormalizedIf, NormalizedThen, fail)) :-
    !,
    source_body(If, NormalizedIf),
    source_body(Then, NormalizedThen).
source_body((Left ; Right), disj(NormalizedLeft, NormalizedRight)) :-
    !,
    source_body(Left, NormalizedLeft),
    source_body(Right, NormalizedRight).
source_body((Left, Right), conj(NormalizedLeft, NormalizedRight)) :-
    !,
    source_body(Left, NormalizedLeft),
    source_body(Right, NormalizedRight).
source_body(\+ Goal, not(NormalizedGoal)) :-
    !,
    source_body(Goal, NormalizedGoal).
source_body(not(Goal), not(NormalizedGoal)) :-
    !,
    source_body(Goal, NormalizedGoal).
source_body(Goal, Goal).

check_goal(Goal) :-
    (   sub_term(Subgoal, Goal),
        nonvar(Subgoal),
        functor(Subgoal, call, Arity),
        Arity > 0
    ->  throw(error(domain_error(call_free_goal, Goal), _))
    ;   true
    ).

ir_to_prolog(mnn_program(_, meta(_, Events), Predicates, _, _), Terms) :-
    event_terms(Events, Predicates, Terms).

event_terms([], _, []).
event_terms([directive(_, Directive)|Events], Predicates, [(:- Directive)|Terms]) :-
    event_terms(Events, Predicates, Terms).
event_terms([clause(Id)|Events], Predicates, [Term|Terms]) :-
    clause_term(Id, Predicates, Term),
    event_terms(Events, Predicates, Terms).

clause_term(Id, Predicates, Term) :-
    member(mnn_pred(_, _, _, Clauses, _), Predicates),
    member(mnn_clause(Id, Head, Body, _), Clauses),
    !,
    prolog_body(Body, Goal),
    (   Goal == true
    ->  Term = Head
    ;   Term = (Head :- Goal)
    ).

prolog_body(ite(If, Then, Else), (PrologIf -> PrologThen ; PrologElse)) :-
    !,
    prolog_body(If, PrologIf),
    prolog_body(Then, PrologThen),
    prolog_body(Else, PrologElse).
prolog_body(disj(Left, Right), (PrologLeft ; PrologRight)) :-
    !,
    prolog_body(Left, PrologLeft),
    prolog_body(Right, PrologRight).
prolog_body(conj(Left, Right), (PrologLeft, PrologRight)) :-
    !,
    prolog_body(Left, PrologLeft),
    prolog_body(Right, PrologRight).
prolog_body(not(Goal), \+ PrologGoal) :-
    !,
    prolog_body(Goal, PrologGoal).
prolog_body(Goal, Goal).

emit_program(Program, File) :-
    ir_to_prolog(Program, Terms),
    setup_call_cleanup(
        open(File, write, Stream),
        write_terms(Stream, Terms),
        close(Stream)).

write_terms(_, []) :-
    !.
write_terms(Stream, [Term|Terms]) :-
    !,
    write_term(Stream, Term, [quoted(true), numbervars(true)]),
    write(Stream, '.\n\n'),
    write_terms(Stream, Terms).

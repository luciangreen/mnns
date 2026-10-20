:- module(prolog2ann_parse,
          [ parse_file/3
          ]).

:- use_module(library(error)).

%% parse_file(+SourceFile, +DomainFile, -Parsed) is det.
%
%  Read a Prolog source file and an optional domain file. Use `none` when no
%  domain file is supplied. Parsed clauses preserve variable names and source
%  locations.
%
%  @example
%    ?- parse_file('rules.pl', none, Parsed).
parse_file(SourceFile, DomainFile, ann_source(SourceFile, Clauses, Domains)) :-
    must_be(atom, SourceFile),
    read_source(SourceFile, Clauses),
    read_domain_file(DomainFile, Domains).

read_source(File, Clauses) :-
    setup_call_cleanup(
        open(File, read, Stream),
        read_source_terms(Stream, File, 1, Clauses),
        close(Stream)).

read_source_terms(Stream, File, Id, Clauses) :-
    read_term(Stream, Term,
              [ syntax_errors(error),
                term_position(TermPosition),
                variable_names(VariableNames),
                module(prolog2ann_parse)
              ]),
    stream_position_data(line_count, TermPosition, Line),
    (   Term == end_of_file
    ->  Clauses = []
    ;   source_clause(Term, File, Line, Id, VariableNames, Clause),
        (   Clause == skip
        ->  Clauses = Rest
        ;   Clauses = [Clause|Rest]
        ),
        NextId is Id + 1,
        read_source_terms(Stream, File, NextId, Rest)
    ).

source_clause((:- module(_, _)), _, _, _, _, skip) :-
    !.
source_clause((:- module(_)), _, _, _, _, skip) :-
    !.
source_clause((:- _Directive), File, Line, _, _, _) :-
    !,
    unsupported(directive, File, Line).
source_clause((Head :- Body), File, Line, Id, Names,
              ann_clause(Id, Head, Body, Names, File, Line)) :-
    !,
    (   callable(Head),
        \+ var(Head)
    ->  true
    ;   throw(error(type_error(callable_head, Head), file(File, Line)))
    ),
    validate_body(Body, File, Line).
source_clause(Term, File, Line, Id, Names,
              ann_clause(Id, Term, true, Names, File, Line)) :-
    callable(Term),
    !.
source_clause(Term, File, Line, _, _, _) :-
    throw(error(type_error(prolog_clause, Term), file(File, Line))).

validate_body((Left, Right), File, Line) :-
    !,
    validate_body(Left, File, Line),
    validate_body(Right, File, Line).
validate_body((Left ; Right), File, Line) :-
    !,
    validate_body(Left, File, Line),
    validate_body(Right, File, Line).
validate_body((If -> Then), File, Line) :-
    !,
    unsupported((If -> Then), File, Line).
validate_body((If *-> Then), File, Line) :-
    !,
    unsupported((If *-> Then), File, Line).
validate_body(\+ Goal, File, Line) :-
    !,
    validate_negated_goal(Goal, File, Line).
validate_body(not(Goal), File, Line) :-
    !,
    validate_negated_goal(Goal, File, Line).
validate_body(Goal, File, Line) :-
    callable(Goal),
    !,
    validate_goal(Goal, File, Line).
validate_body(Goal, File, Line) :-
    unsupported(Goal, File, Line).

validate_negated_goal(Goal, File, Line) :-
    (   callable(Goal),
        Goal \= (_ , _),
        Goal \= (_ ; _),
        Goal \= (_ -> _),
        functor(Goal, Name, _),
        Name \== '\\+'
    ->  validate_goal(Goal, File, Line)
    ;   unsupported(Goal, File, Line)
    ).

validate_goal(!, File, Line) :-
    !,
    unsupported(!, File, Line).
validate_goal(Goal, File, Line) :-
    functor(Goal, Name, Arity),
    unsupported_builtin(Name, Arity, Construct),
    !,
    unsupported(Construct, File, Line).
validate_goal(Goal, File, Line) :-
    functor(Goal, Name, Arity),
    system_predicate(Name, Arity),
    \+ supported_builtin(Name, Arity),
    !,
    unsupported(Goal, File, Line).
validate_goal(_, _, _).

supported_builtin(true, 0).
supported_builtin(fail, 0).
supported_builtin(false, 0).
supported_builtin('=', 2).
supported_builtin('\\=', 2).
supported_builtin('==', 2).
supported_builtin('\\==', 2).
supported_builtin(is, 2).
supported_builtin('<', 2).
supported_builtin('=<', 2).
supported_builtin('>', 2).
supported_builtin('>=', 2).
supported_builtin('=:=', 2).
supported_builtin('=\\=', 2).

unsupported_builtin(!, 0, !).
unsupported_builtin(findall, 3, findall/3).
unsupported_builtin(bagof, 3, bagof/3).
unsupported_builtin(setof, 3, setof/3).
unsupported_builtin(assert, 1, assert/1).
unsupported_builtin(asserta, 1, asserta/1).
unsupported_builtin(assertz, 1, assertz/1).
unsupported_builtin(retract, 1, retract/1).
unsupported_builtin(retractall, 1, retractall/1).
unsupported_builtin(abolish, 1, abolish/1).
unsupported_builtin(write, 1, write/1).
unsupported_builtin(writeq, 1, writeq/1).
unsupported_builtin(writeln, 1, writeln/1).
unsupported_builtin(format, 2, format/2).
unsupported_builtin(format, 3, format/3).
unsupported_builtin(read, 1, read/1).
unsupported_builtin(read_term, 2, read_term/2).
unsupported_builtin(read_term, 3, read_term/3).
unsupported_builtin(open, 3, open/3).
unsupported_builtin(close, 1, close/1).
unsupported_builtin(nl, 0, nl/0).
unsupported_builtin(put_char, 1, put_char/1).
unsupported_builtin(get_char, 1, get_char/1).
unsupported_builtin(call, 1, call/1).
unsupported_builtin(catch, 3, catch/3).
unsupported_builtin(throw, 1, throw/1).
unsupported_builtin(once, 1, once/1).
unsupported_builtin(repeat, 0, repeat/0).

system_predicate(Name, Arity) :-
    functor(Goal, Name, Arity),
    once(predicate_property(system:Goal, built_in)).

unsupported(Construct, File, Line) :-
    throw(error(unsupported_construct(Construct), file(File, Line))).

read_domain_file(none, []) :-
    !.
read_domain_file(File, Domains) :-
    must_be(atom, File),
    setup_call_cleanup(
        open(File, read, Stream),
        read_domain_terms(Stream, File, 1, Domains),
        close(Stream)).

read_domain_terms(Stream, File, Id, Domains) :-
    read_term(Stream, Term,
              [ syntax_errors(error),
                term_position(TermPosition),
                module(prolog2ann_parse)
              ]),
    stream_position_data(line_count, TermPosition, Line),
    (   Term == end_of_file
    ->  Domains = []
    ;   domain_declaration(Term, File, Line, Domain),
        Domains = [Domain|Rest],
        NextId is Id + 1,
        read_domain_terms(Stream, File, NextId, Rest)
    ).

domain_declaration(domain(Name, Values), _, _, domain(Name, Values)) :-
    atom(Name),
    is_list(Values),
    ground(Values),
    !.
domain_declaration(range(Name, Low, High), _, _, range(Name, Low, High)) :-
    atom(Name),
    integer(Low),
    integer(High),
    Low =< High,
    !.
domain_declaration(Term, File, Line, _) :-
    unsupported(Term, File, Line).

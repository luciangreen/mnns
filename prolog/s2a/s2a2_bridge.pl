/*  s2a2_bridge.pl -- S2A specs solved by S2A2 when mnns's own s2a/4 finds nothing.

    s2a2(+Name, +Spec, +Options, -Result)
        Spec has the form s2a/4 takes: [[[input,[['A',In]]],[output,[['B',Out]]]], ...].
        1. mnns's s2a/4 runs first, without a table, so every case it already solves gives
           exactly the program it gave before.
        2. When it returns no_algorithm(_), S2A2's io_synth (github.com/luciangreen/S2A2,
           prolog/io_synth.pl) is asked for a program from the same examples: structural
           signals, top-down propagation (map, filter, templates, foldr, with invented helper
           predicates), observational equivalence, types, its own projection and exact
           polynomials, and a genetic algorithm last.
        3. If S2A2 finds nothing too, and allow_table(true) is given, s2a/4 builds its table.
        Result is an mnn_program/5 in the mnns IR, or s2a/4's no_algorithm(Reason).

    Options
        allow_table(Bool)              as for s2a/4
        reference(Clauses, RefName)    also prove the program equal to a reference program,
                                       for every input of its types, with S2A2's io_proof.pl;
                                       the proof is put in the trace
        types(Types)                   argument types for the proof (default: from the examples)
        ga(Bool)                       let S2A2 use its genetic algorithm (default true)
        time_limit(Seconds)            for S2A2's search (default 60)
        s2a2_home(Dir)                 where S2A2 is (default: $S2A2_HOME, then ../S2A2 or
                                       ../s2a2 beside this repository)

    s2a2_available/0 succeeds when S2A2 can be loaded.

    The proof field of the program stays proof([]): S2A2's proofs are in S2A2's own terms,
    which mnns's proof checker does not read. Every program S2A2 returns has been run on
    every example; with reference/2 the trace also holds proved(Steps) or not_proved.
*/
:- module(mnn_s2a2, [s2a2/4, s2a2_available/0]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(time)).
:- use_module(s2a).

:- dynamic loaded_home/1.

s2a2(Name, Spec, Options, Result) :-
    (   \+ is_list(Options) -> Result = no_algorithm(invalid_options)
    ;   \+ maplist(valid_option, Options) -> Result = no_algorithm(invalid_options)
    ;   mnn_s2a:s2a(Name, Spec, [], R0),
        (   R0 = no_algorithm(Reason), \+ fatal(Reason)
        ->  (   s2a2_program(Name, Spec, Options, R1)
            ->  Result = R1
            ;   memberchk(allow_table(true), Options)
            ->  mnn_s2a:s2a(Name, Spec, [allow_table(true)], Result)
            ;   Result = R0 )
        ;   Result = R0 )
    ), !.

% problems with the spec itself, which S2A2 cannot mend
fatal(invalid_name).
fatal(invalid_spec).
fatal(empty_spec).
fatal(invalid_options).
fatal(unsupported_spec_shape).
fatal(conflicting_examples(_)).

valid_option(allow_table(B)) :- memberchk(B, [true, false]).
valid_option(reference(Cs, N)) :- is_list(Cs), atom(N).
valid_option(types(Ts)) :- is_list(Ts).
valid_option(ga(B)) :- memberchk(B, [true, false]).
valid_option(time_limit(S)) :- number(S), S > 0.
valid_option(s2a2_home(D)) :- atom(D).

% ---------------------------------------------------------------- loading S2A2
s2a2_available :- s2a2_available([]).
s2a2_available(Options) :- catch(load_s2a2(Options), _, fail).

load_s2a2(Options) :-
    s2a2_home(Options, Home),
    (   loaded_home(Home) -> true
    ;   directory_file_path(Home, 'prolog/io_synth.pl', Synth), exists_file(Synth),
        directory_file_path(Home, 'prolog/io_proof.pl', Proof),
        use_module(Synth, []), use_module(Proof, []),
        assertz(loaded_home(Home)) ).

s2a2_home(Options, Home) :- memberchk(s2a2_home(Home), Options), !.
s2a2_home(_, Home) :- getenv('S2A2_HOME', Home), Home \== '', !.
s2a2_home(_, Home) :-
    module_property(mnn_s2a2, file(F)), file_directory_name(F, D1),   % prolog/s2a
    file_directory_name(D1, D2), file_directory_name(D2, Root),       % the mnns root
    file_directory_name(Root, Parent),
    member(N, ['S2A2', s2a2]), directory_file_path(Parent, N, Home),
    exists_directory(Home), !.

% ---------------------------------------------------------------- S2A2's program in the IR
s2a2_program(Name, Spec, Options, Program) :-
    s2a2_available(Options),
    maplist(mnn_s2a:example_pair, Spec, Pairs0), sort(Pairs0, Pairs),
    findall(I-O, member(pair(I, O), Pairs), Exs),
    ( memberchk(ga(GA), Options) -> true ; GA = true ),
    ( memberchk(time_limit(T), Options) -> true ; T = 60 ),
    catch(call_with_time_limit(T, io_synth:synth(Name, Exs, [ga(GA)], Clauses, report(Tree, _, _))), _, fail),
    proof_trace(Clauses, Name, Exs, Options, ProofTrace),
    length(Exs, Count),
    to_ir(Name, Clauses, Tree, Count, ProofTrace, Program).

proof_trace(Clauses, Name, Exs, Options, [s2a2_proof(RefName, Proof)]) :-
    memberchk(reference(Ref, RefName), Options), !,
    (   memberchk(types(Types), Options) -> true
    ;   io_synth:signals(Exs, [in_type(IT)|_]), Types = [IT, any] ),
    io_proof:prove_equal(Clauses, Name, Ref, RefName, Types, Proof).
proof_trace(_, _, _, _, []).

to_ir(Name, Clauses, Tree, Count, ProofTrace,
      mnn_program(Module, meta(s2a2_io_synth(Name, Kind), Events), Preds, proof([]),
                  trace([s2a2_io_synth(Name, Kind, examples_reproduced(Count))|ProofTrace]))) :-
    atom_concat(mnn_s2a2_, Name, Module),
    Tree = node(_, Kind0, _), functor(Kind0, Kind, _),
    length(Clauses, N), N1 is N + 1, numlist(2, N1, Ids),
    maplist([C, Id, K-mnn_clause(Id, H, B, generated(s2a2_io_synth, Id))]>>
                ( ( C = (H :- B) -> true ; H = C, B = true ), functor(H, F, A), K = F/A ),
            Clauses, Ids, Keyed),
    findall(K, member(K-_, Keyed), Ks0), list_to_set(Ks0, Ks),
    maplist(pred_of(Keyed), Ks, Preds),
    findall(clause(Id), member(Id, Ids), ClauseEvents),
    Events = [directive(1, module(Module, [Name/2]))|ClauseEvents].

pred_of(Keyed, F/A, mnn_pred(F/A, Modes, Domains, Cs, original)) :-
    findall(C, member(F/A-C, Keyed), Cs),
    length(Modes, A), maplist(=('?'), Modes), length(Domains, A), maplist(=(any), Domains).

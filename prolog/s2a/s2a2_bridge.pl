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
                                       for every input of its types. The proof is an mnns
                                       proof, proof([proof_step(1, induction_equivalence, [],
                                       equivalent(domain(types(Types)), modes(all)))]), that
                                       mnns's own checker accepts against the reference
                                       (check_proof(Program, Reference, Proof, accepted));
                                       the reference, as an mnn_program, is in the trace as
                                       s2a2_reference(Reference)
        types(Types)                   argument types for the proof (default: from the examples)
        ga(Bool)                       let S2A2 use its genetic algorithm (default true)
        time_limit(Seconds)            for S2A2's search (default 60)
        s2a2_home(Dir)                 where S2A2 is (default: $S2A2_HOME, then ../S2A2 or
                                       ../s2a2 beside this repository)

    s2a2_available/0 succeeds when S2A2 can be loaded.

    Without reference/2 the proof field is proof([]): there is nothing to prove the program
    equal to, but every program S2A2 returns has been run on every example.

    Optimisation with S2A2
      s2a2_learn(+Pairs, +Options, -Algorithm)
          Pairs = [pair(Before, After, Targets)], Before and After mnn_programs and Targets
          a list of Name/Arity: S2A2's learn/2 finds an optimisation algorithm (operators
          with conditions learned from the pairs).
      s2a2_apply(+Algorithm, +Program, +Targets, +Options, -Result)
          S2A2's apply_algorithm/5 on an mnn_program. Result is an mnn_program whose trace
          holds the steps and S2A2's prover's verdict on the targets (proved(syntactic(_)),
          proved(exhaustive(N)) over every input built from the input predicates, or
          refuted(...)). When it is proved, the proof field is an mnns proof of rule
          edb_equivalence (domain all for a syntactic proof, else edb(Preds, Consts)), kept
          only if mnns's checker, repeating the check with its own copy of S2A2's prover,
          accepts it; otherwise proof([]).
      s2a2_derive(+Spec, +Mode, +Options, -Result)
          fold.pl's spec to algorithm on an mnn_program whose main predicate is the target:
          a faster program (accumulator, tupling, fusion, deforestation). It is returned only
          when fold.pl's verify/5 shows it total and the specification functional, which
          makes them equal on every input of Mode (for example [in(list(int)), out]); the
          trace holds the strategy, the lemmas, the verdict and a bounded check. The proof
          field is an mnns proof of rule fold_derivation, kept only if mnns's checker,
          repeating the derivation and verify/5 with its own copy of fold.pl, accepts it.
*/
:- module(mnn_s2a2, [s2a2/4, s2a2_available/0, s2a2_learn/3, s2a2_apply/5, s2a2_derive/4]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(time)).
:- use_module(s2a).
:- use_module('../proof/proof_checker').

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
        forall(member(F, ['prolog/s2a2.pl', 'prolog/prover.pl', 'prolog/fold.pl']),
               ( directory_file_path(Home, F, P), use_module(P, []) )),
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
    length(Exs, Count),
    Tree = node(_, Kind0, _), functor(Kind0, Kind, _),
    ir_of(Name, Clauses, s2a2_io_synth(Name, Kind), [s2a2_io_synth(Name, Kind, examples_reproduced(Count))],
          proof([]), Program0),
    with_reference(Program0, Exs, Options, Program).

% with_reference(+Program0, +Examples, +Options, -Program): the mnns proof against a reference
with_reference(P0, Exs, Options, P) :-
    memberchk(reference(Ref, RefName), Options), !,
    (   memberchk(types(Types0), Options) -> true
    ;   io_synth:signals(Exs, [in_type(IT)|_]), Types0 = [IT, any] ),
    copy_term(Types0, Types), term_variables(Types, Vs), maplist(=(any), Vs),
    ir_of(RefName, Ref, s2a2_reference(RefName), [], proof([]), RefIR),
    Proof = proof([proof_step(1, induction_equivalence, [], equivalent(domain(types(Types)), modes(all)))]),
    P0 = mnn_program(M, Meta, Preds, _, trace(T0)),
    P1 = mnn_program(M, Meta, Preds, Proof, trace(T1)),
    append(T0, [s2a2_reference(RefIR)], T1),
    (   mnn_proof_checker:check_proof(P1, RefIR, Proof, accepted)
    ->  P = P1
    ;   append(T0, [s2a2_proof(RefName, not_proved)], T2), P = mnn_program(M, Meta, Preds, proof([]), trace(T2)) ).
with_reference(P, _, _, P).

% ir_of(+Name, +Clauses, +MetaTerm, +Trace, +Proof, -Program): clauses as an mnn_program
% exporting Name/2 (Name/N for the arity of its first clause)
ir_of(Name, Clauses, MetaTerm, Trace, Proof,
      mnn_program(Module, meta(MetaTerm, Events), Preds, Proof, trace(Trace))) :-
    atom_concat(mnn_s2a2_, Name, Module),
    length(Clauses, N), N1 is N + 1, numlist(2, N1, Ids),
    maplist([C, Id, K-mnn_clause(Id, H, B, generated(s2a2, Id))]>>
                ( ( C = (H :- B) -> true ; H = C, B = true ), functor(H, F, A), K = F/A ),
            Clauses, Ids, Keyed),
    findall(K, member(K-_, Keyed), Ks0), list_to_set(Ks0, Ks),
    maplist(pred_of(Keyed), Ks, Preds),
    (   memberchk(Name/Ar, Ks) -> true ; Ar = 2 ),
    findall(clause(Id), member(Id, Ids), ClauseEvents),
    Events = [directive(1, module(Module, [Name/Ar]))|ClauseEvents].

pred_of(Keyed, F/A, mnn_pred(F/A, Modes, Domains, Cs, original)) :-
    findall(C, member(F/A-C, Keyed), Cs),
    length(Modes, A), maplist(=('?'), Modes), length(Domains, A), maplist(=(any), Domains).

% ---------------------------------------------------------------- optimisation with S2A2
main_key(mnn_program(_, meta(_, Events), _, _, _), Key) :- memberchk(directive(_, module(_, [Key])), Events).
ir_clauses(mnn_program(_, _, Preds, _, _), Clauses) :-
    findall(C, ( member(mnn_pred(_, _, _, Cs, _), Preds), member(mnn_clause(_, H, B, _), Cs),
                 ( B == true -> C = H ; C = (H :- B) ) ), Clauses).
ir_prog(IR, Prog) :- ir_clauses(IR, Cs), s2a2:program_from_clauses(Cs, Prog).

s2a2_learn(Pairs, Options, Algorithm) :-
    s2a2_available(Options),
    findall(pair(B, A, T), ( member(pair(BI, AI, T), Pairs), ir_prog(BI, B), ir_prog(AI, A) ), SPairs),
    ( memberchk(time_limit(TL), Options) -> true ; TL = 600 ),
    catch(call_with_time_limit(TL, s2a2:learn(SPairs, Algorithm)), _, fail).

s2a2_apply(Algorithm, Program, Targets, Options, Result) :-
    s2a2_available(Options),
    ir_prog(Program, P0),
    s2a2:apply_algorithm(Algorithm, P0, Targets, P1, Steps),
    s2a2:program_to_clauses(P1, Cs),
    verdict_of(P0, P1, Targets, Verdict, Domain),
    main_key(Program, Name/_),
    atom_concat(Name, '_opt', OptName),
    ir_of(OptName, Cs, s2a2_algorithm(Name), [s2a2_apply(Steps), s2a2_prover(Verdict)], proof([]), R0),
    % the program keeps its predicate names: export the original main predicate
    R0 = mnn_program(_, meta(MT, [directive(I, module(_, _))|Es]), Preds, Pf, Tr),
    main_key(Program, Key), atom_concat(mnn_s2a2_, OptName, Mod),
    R1 = mnn_program(Mod, meta(MT, [directive(I, module(Mod, [Key]))|Es]), Preds, Pf, Tr),
    with_proof(R1, Program, proof([proof_step(1, edb_equivalence, [],
                                              equivalent(domain(Domain), modes(targets(Targets))))]),
               Result).

% S2A2's prover on the rules, over every input built from the input predicates (the facts'
% predicates that no rule defines) and up to three of the facts' constants, as S2A2 does
% with_proof(+Program, +Original, +Proof, -Result): Program with Proof, if mnns's own checker
% accepts Proof against Original; otherwise Program unchanged (proof([]))
with_proof(P, _, proof([proof_step(_, _, _, equivalent(domain(none), _))]), P) :- !.
with_proof(mnn_program(M, Meta, Preds, _, Tr), Original, Proof, Result) :-
    P1 = mnn_program(M, Meta, Preds, Proof, Tr),
    (   catch(mnn_proof_checker:check_proof(P1, Original, Proof, accepted), _, fail)
    ->  Result = P1
    ;   Result = mnn_program(M, Meta, Preds, proof([]), Tr) ).

verdict_of(P0, P1, Targets, Verdict, Domain) :-
    P0 = prog(F, _),
    findall(N/A, ( member(Fa, F), functor(Fa, N, A) ), E0), sort(E0, Edb),
    findall(X, ( member(Fa, F), Fa =.. [_|As], member(X, As) ), X0), sort(X0, Xs),
    ( length(Xs, NX), NX > 3 -> length(Consts, 3), append(Consts, _, Xs) ; Consts = Xs ),
    s2a2:program_to_clauses(P0, C0), s2a2:program_to_clauses(P1, C1),
    include([C]>>(C = (_ :- _)), C0, R0), include([C]>>(C = (_ :- _)), C1, R1),
    (   catch(call_with_time_limit(60, prover:equivalent(R0, R1, Targets, edb(Edb, Consts), V)), _, fail)
    ->  Verdict = V ; Verdict = unknown ),
    (   Verdict = proved(syntactic(_)) -> Domain = all
    ;   Verdict = proved(_) -> Domain = edb(Edb, Consts)
    ;   Domain = none ).

s2a2_derive(Spec, Mode, Options, Result) :-
    s2a2_available(Options),
    main_key(Spec, Target), Target = Name/_,
    ir_clauses(Spec, Cs), fold:clauses(Cs, S),
    ( memberchk(bound(Size), Options) -> true ; Size = 4 ),
    (   catch(call_with_time_limit(120, fold:spec_to_algorithm(S, Target, [], P0, report(St, _, Used, _, _))), _, fail)
    ->  fold:verify(S, P0, Target, Mode, verdict(total(T), functional(F), typed_answers(Ty), _, PF)),
        (   T == yes, F == yes
        ->  fold:bounded_equal(S, Target, PF, Target, Mode, Size, B),
            findall(C, ( member(H-Bd, PF), ( Bd == [] -> C = H ; list_conj(Bd, BC), C = (H :- BC) ) ), PCs),
            ir_of(Name, PCs, s2a2_fold(Name, St),
                  [s2a2_fold(St, lemmas(Used), total(T), functional(F), typed_answers(Ty), bounded(B))],
                  proof([]), R0),
            with_proof(R0, Spec, proof([proof_step(1, fold_derivation, [], equivalent(domain(mode(Mode)), modes(Mode)))]),
                       Result)
        ;   Result = no_algorithm(not_proved(total(T), functional(F))) )
    ;   Result = no_algorithm(no_derivation) ).
list_conj([G], G) :- !.
list_conj([G|Gs], (G, C)) :- list_conj(Gs, C).

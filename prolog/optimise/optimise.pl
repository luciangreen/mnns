/*  optimise.pl - one command that applies every proof-checked optimisation

    optimise_program(+Program, -Optimised, -Report)
    optimise_file(+InFile, +OutFile, -Report)

    Stages, in order (each keeps the program as it was if it fails or its
    proof is not accepted):
      1. PLOp     mnn_plop:optimize_program/3 (proof-checked finite-generator
                  findall-to-fold conversion)
      2. AIOC     mnn_aioc_simplify:simplify_program/4 (proof-checked removal of
                  redundant true/fail and once(true)/once(fail))
      3. Detlog   mnn_detlog_transform:transform_program/3 (green cuts removed,
                  cuts and once/1 compiled to if-then-else). Its report becomes
                  a proof (remove_green_cut, compile_cut, compile_once), and the
                  result is kept only if mnn_proof_checker accepts it.

    Report = optimise_report(Stages, size(Before, After))
      Stages = [plop(Status, Events), simplify(Changes), detlog(Status, Steps)]
      detlog Status = unchanged | proved | rejected(Reason) | failed
      Before, After = program_size(...) from mnn_aioc_size

    Command line (see ../../optimise.pl):
      swipl optimise.pl INPUT.pl OUTPUT.pl
*/

:- module(mnn_optimise,
          [ optimise_program/3,
            optimise_file/3,
            optimise_report_line/2
          ]).

:- use_module('../ir/ir').
:- use_module('../plop/plop').
:- use_module('../aioc/simplify').
:- use_module('../aioc/size').
:- use_module('../detlog/detlog_transform').
:- use_module('../proof/proof_checker').

optimise_program(Program, Optimised,
                 optimise_report([PlopStage, SimplifyStage, DetlogStage],
                                 size(Before, After))) :-
    mnn_aioc_size:measure_program_size(Program, Before),
    plop_stage(Program, AfterPlop, PlopStage),
    simplify_stage(AfterPlop, AfterSimplify, SimplifyStage),
    detlog_stage(AfterSimplify, Optimised, DetlogStage),
    mnn_aioc_size:measure_program_size(Optimised, After).

%   Detlog, kept only with an accepted proof.
detlog_stage(Program, Optimised, detlog(Status, Steps)) :-
    (   catch(mnn_detlog_transform:transform_program(
                  Program, Candidate, detlog_transform_report(Events)),
              Error,
              ( print_message(warning, Error), fail ))
    ->  detlog_proof_steps(Events, 1, Steps),
        (   Steps == []
        ->  Optimised = Program,
            Status = unchanged
        ;   mnn_proof_checker:check_proof(Candidate, Program, proof(Steps), Result),
            (   Result == accepted
            ->  Optimised = Candidate,
                Status = proved
            ;   Optimised = Program,
                Status = rejected(Result)
            )
        )
    ;   Optimised = Program,
        Status = failed,
        Steps = []
    ).

detlog_proof_steps([], _, []).
detlog_proof_steps([Event|Events], N, Steps) :-
    (   detlog_event_rule(Event, Rule)
    ->  Steps = [proof_step(N, Rule, [], equivalent(domain(all), modes(all)))|Rest],
        N1 is N + 1
    ;   Steps = Rest,
        N1 = N
    ),
    detlog_proof_steps(Events, N1, Rest).

detlog_event_rule(removed_green_cut(_, _), remove_green_cut).
detlog_event_rule(compiled_cut(_, _, _), compile_cut).
detlog_event_rule(compiled_once(_, _, _), compile_once).

plop_stage(Program, Optimised, plop(Status, Events)) :-
    (   catch(mnn_plop:optimize_program(Program, Candidate,
                                        plop_report(Events, _Proof, Status)),
              Error,
              ( print_message(warning, Error), fail ))
    ->  Optimised = Candidate
    ;   Optimised = Program,
        Status = failed,
        Events = []
    ).

simplify_stage(Program, Optimised, simplify(Changes)) :-
    (   catch(mnn_aioc_simplify:simplify_program(
                  Program, Candidate, _Proof,
                  simplification_report(changes(Changes), _, _, _)),
              Error,
              ( print_message(warning, Error), fail ))
    ->  Optimised = Candidate
    ;   Optimised = Program,
        Changes = failed
    ).

optimise_file(InFile, OutFile, Report) :-
    mnn_ir:parse_program(InFile, Program),
    optimise_program(Program, Optimised, Report),
    emit_optimised(Optimised, OutFile).

%!  emit_optimised(+Program, +File) is det.
%   Writes the directives, then every clause of every predicate.
%   mnn_ir:emit_program/2 writes only clauses recorded in the source events,
%   so it would drop clauses that PLOp rewrote or generated (for example
%   mnn_loop2_1/2); this writes them all.
emit_optimised(mnn_program(_, meta(_, Events), Predicates, _, _), File) :-
    findall((:- Directive), member(directive(_, Directive), Events), Directives),
    findall(Term,
            ( member(mnn_pred(_, _, _, Clauses, _), Predicates),
              member(mnn_clause(_, Head, Body, _), Clauses),
              clause_term(Head, Body, Term)
            ),
            ClauseTerms),
    append(Directives, ClauseTerms, Terms),
    setup_call_cleanup(
        open(File, write, Stream),
        forall(member(T, Terms),
               ( write_term(Stream, T, [quoted(true), numbervars(true)]),
                 write(Stream, '.\n\n') )),
        close(Stream)).

clause_term(Head, Body, Term) :-
    mnn_ir:prolog_body(Body, Goal),
    (   Goal == true
    ->  Term = Head
    ;   Term = (Head :- Goal)
    ).

%!  optimise_report_line(+Report, -Line) is det.
%   One line for tools such as fastos:
%   MNN_OPTIMISE ok changed=true size_before=N size_after=M plop=accepted simplify=2 detlog=proved detlog_steps=3
optimise_report_line(optimise_report([plop(Status, _), simplify(Changes),
                                      detlog(DetlogStatus, Steps)],
                                     size(Before, After)),
                     Line) :-
    weighted_total(Before, B),
    weighted_total(After, A),
    (   ( Status == accepted ; integer(Changes), Changes > 0 ; DetlogStatus == proved )
    ->  Changed = true
    ;   Changed = false
    ),
    length(Steps, NSteps),
    detlog_status_word(DetlogStatus, DetlogWord),
    format(string(Line),
           "MNN_OPTIMISE ok changed=~w size_before=~w size_after=~w plop=~w simplify=~w detlog=~w detlog_steps=~w",
           [Changed, B, A, Status, Changes, DetlogWord, NSteps]).

detlog_status_word(rejected(_), rejected) :- !.
detlog_status_word(Status, Status).

weighted_total(program_size(_, _, _, _, weighted_total(Total)), Total).

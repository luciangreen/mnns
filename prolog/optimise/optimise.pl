/*  optimise.pl - one command that applies every proof-checked optimisation

    optimise_program(+Program, -Optimised, -Report)
    optimise_file(+InFile, +OutFile, -Report)

    Stages, in order (each keeps the program as it was if it fails or its
    proof is not accepted):
      1. PLOp     mnn_plop:optimize_program/3 (proof-checked finite-generator
                  findall-to-fold conversion)
      2. AIOC     mnn_aioc_simplify:simplify_program/4 (proof-checked removal of
                  redundant true/fail and once(true)/once(fail))

    Detlog's transform is not used: its rewrites are not machine-checked.

    Report = optimise_report(Stages, size(Before, After))
      Stages = [plop(Status, Events), simplify(Changes)]
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

optimise_program(Program, Optimised,
                 optimise_report([PlopStage, SimplifyStage], size(Before, After))) :-
    mnn_aioc_size:measure_program_size(Program, Before),
    plop_stage(Program, AfterPlop, PlopStage),
    simplify_stage(AfterPlop, Optimised, SimplifyStage),
    mnn_aioc_size:measure_program_size(Optimised, After).

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
%   MNN_OPTIMISE ok changed=true size_before=N size_after=M plop=accepted simplify=2
optimise_report_line(optimise_report([plop(Status, _), simplify(Changes)],
                                     size(Before, After)),
                     Line) :-
    weighted_total(Before, B),
    weighted_total(After, A),
    (   ( Status == accepted ; integer(Changes), Changes > 0 )
    ->  Changed = true
    ;   Changed = false
    ),
    format(string(Line),
           "MNN_OPTIMISE ok changed=~w size_before=~w size_after=~w plop=~w simplify=~w",
           [Changed, B, A, Status, Changes]).

weighted_total(program_size(_, _, _, _, weighted_total(Total)), Total).

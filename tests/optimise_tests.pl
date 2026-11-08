:- begin_tests(mnn_optimise).

:- use_module('../prolog/optimise/optimise').
:- use_module('../prolog/ir/ir').

%   A finite findall over ground facts: PLOp converts it to a fold.
optimise_source(
"num(1).
num(2).
num(3).
values(Xs) :- findall(X, num(X), Xs).
").

with_source_file(Source, File) :-
    tmp_file_stream(text, File, Stream),
    write(Stream, Source),
    close(Stream).

test(optimise_file_converts_and_reports) :-
    optimise_source(Source),
    with_source_file(Source, In),
    tmp_file(out, Out0),
    atom_concat(Out0, '.pl', Out),
    mnn_optimise:optimise_file(In, Out, Report),
    Report = optimise_report([plop(Status, _), simplify(_), detlog(_, _)], size(_, _)),
    assertion(Status == accepted),
    assertion(exists_file(Out)),
    mnn_optimise:optimise_report_line(Report, Line),
    assertion(sub_string(Line, 0, _, _, "MNN_OPTIMISE ok changed=true")),
    read_file_to_string(Out, Emitted, []),
    (   catch(( load_files(Out, []),
                values(Values) ),
              Error,
              ( format(user_error, "~q~n~s~n", [Error, Emitted]), fail ))
    ->  assertion(Values == [1, 2, 3])
    ;   format(user_error, "Emitted file:~n~s~n", [Emitted]),
        fail
    ),
    assertion(sub_string(Emitted, _, _, _, "mnn_loop2_")).

test(unsupported_program_is_kept, [nondet]) :-
    with_source_file("p(a).\nq(X) :- p(X).\n", In),
    mnn_ir:parse_program(In, Program),
    mnn_optimise:optimise_program(Program, Optimised, Report),
    Report = optimise_report([plop(Status, _), simplify(Changes), detlog(DetlogStatus, _)], _),
    assertion(Status == unchanged),
    assertion(Changes == 0),
    assertion(DetlogStatus == unchanged),
    assertion(Optimised =@= Program).

%   Cuts and once/1: Detlog rewrites them, the proof is checked, and the
%   optimised file gives the same answers.
test(detlog_stage_is_proved_and_keeps_answers) :-
    with_source_file(
"small(X) :- X < 10, !.
pick(X) :- member(X, [1, 2, 3]), X > 1, !.
first(X) :- once(member(X, [a, b, c])).
", In),
    tmp_file(out, Out0),
    atom_concat(Out0, '.pl', Out),
    mnn_optimise:optimise_file(In, Out, Report),
    Report = optimise_report([_, _, detlog(Status, Steps)], _),
    assertion(Status == proved),
    length(Steps, N),
    assertion(N =:= 3),
    mnn_optimise:optimise_report_line(Report, Line),
    assertion(sub_string(Line, _, _, _, "detlog=proved detlog_steps=3")),
    read_file_to_string(Out, Emitted, []),
    assertion(\+ sub_string(Emitted, _, _, _, "!")),
    assertion(\+ sub_string(Emitted, _, _, _, "once(")),
    load_files(Out, [module(detlog_out)]),
    assertion(detlog_out:small(5)),
    assertion(\+ detlog_out:small(20)),
    findall(P, detlog_out:pick(P), Picks),
    assertion(Picks == [2]),
    findall(F, detlog_out:first(F), Firsts),
    assertion(Firsts == [a]).

:- end_tests(mnn_optimise).

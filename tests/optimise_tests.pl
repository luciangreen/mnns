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
    Report = optimise_report([plop(Status, _), simplify(_)], size(_, _)),
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
    Report = optimise_report([plop(Status, _), simplify(Changes)], _),
    assertion(Status == unchanged),
    assertion(Changes == 0),
    assertion(Optimised =@= Program).

:- end_tests(mnn_optimise).

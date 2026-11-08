/*  optimise.pl - optimise a Prolog file with every proof-checked MNN stage

    Usage:  swipl optimise.pl -- INPUT.pl OUTPUT.pl

    Prints one line:
      MNN_OPTIMISE ok changed=true size_before=40 size_after=36 plop=accepted simplify=0 detlog=proved detlog_steps=2
    or, if the file could not be optimised (for example, syntax outside the
    supported subset):
      MNN_OPTIMISE error <message>
    and exits with status 1. OUTPUT.pl is only written on success.
    See prolog/optimise/optimise.pl.
*/

:- use_module(library(main)).
:- use_module('prolog/optimise/optimise').

:- initialization(main, main).

main([In, Out]) :-
    !,
    catch(optimise(In, Out), Error, failed(Error)).
main(_) :-
    format(user_error, "Usage: swipl optimise.pl -- INPUT.pl OUTPUT.pl~n", []),
    halt(2).

optimise(In, Out) :-
    mnn_optimise:optimise_file(In, Out, Report),
    mnn_optimise:optimise_report_line(Report, Line),
    format("~s~n", [Line]).

failed(Error) :-
    format(string(Message), "~q", [Error]),
    split_string(Message, "\n", "", [FirstLine|_]),
    format("MNN_OPTIMISE error ~s~n", [FirstLine]),
    halt(1).

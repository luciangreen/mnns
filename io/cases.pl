% The predicates whose inputs and outputs are recorded in io/ios.txt (see io/ios_engine.pl).
:- ios_engine:load_repo('prolog/optimise/optimise').
:- ios_engine:load_repo('prolog/s2a/s2a').
:- use_module(library(readutil)).

io_title('mnns').

io_cases([optimise_file, s2a]).

% Small programs to optimise, made from parts.
program(K, Text) :-
    num(K, 1, 1, 6, Kind),
    pick(K, 2, [num, item, val, n], F),
    pick_n(K, 3, 5, [1, 2, 3, 4, 5, 7, 9], Ns),
    maplist([N, L]>>format(string(L), "~w(~w).", [F, N]), Ns, Ls), atomic_list_concat(Ls, '\n', Facts),
    template(Kind, F, Rules),
    format(string(Text), "~w~n~w~n", [Facts, Rules]).

template(1, F, R) :- format(string(R), "values(Xs) :- findall(X, ~w(X), Xs).", [F]).
template(2, F, R) :- format(string(R), "total(T) :- findall(X, ~w(X), Xs), sum_list(Xs, T).", [F]).
template(3, _, "sum([], 0).\nsum([X|Xs], S) :- sum(Xs, S0), S is S0 + X.").
template(4, _, "len([], 0).\nlen([_|T], N) :- len(T, N0), N is N0 + 1.").
template(5, F, R) :- format(string(R), "doubled(Ys) :- findall(Y, (~w(X), Y is X * 2), Ys).", [F]).
template(6, _, "app([], L, L).\napp([H|T], L, [H|R]) :- app(T, L, R).").

% Examples for spec to algorithm: inputs and the outputs wanted.
spec(K, Spec) :-
    num(K, 4, 1, 4, Kind),
    pick_n(K, 5, 3, [[5,6], [7,8], [1,2], [3,9], [4,4]], Pairs),
    sort(Pairs, Ps),
    maplist(spec_pair(Kind), Ps, Spec).
spec_pair(1, [A,B], [[input, [['A', [A,B]]]], [output, [['B', [B,A]]]]]).
spec_pair(2, [A,B], [[input, [['A', A]]], [output, [['B', B]]]]).
spec_pair(3, [A,B], [[input, [['A', A], ['B', B]]], [output, [['C', S]]]]) :- S is A + B.
spec_pair(4, [A,_], [[input, [['A', A]]], [output, [['B', D]]]]) :- D is A * 2.

io_input(optimise_file, K, [Program]) :- program(K, Program).
io_input(s2a, K, [Name, Spec, Options]) :- pick(K, 6, [probe_a, probe_b, swap_probe], Name), spec(K, Spec), pick(K, 7, [[], [allow_table(true)]], Options).

% optimises a program file; the report line and the clauses written (variables named in order)
io_run(optimise_file, [Program], [report(Line), emitted(Emitted)]) :-
    In = '/tmp/mnns_ios_in.pl', Out = '/tmp/mnns_ios_out.pl',
    setup_call_cleanup(open(In, write, S), write(S, Program), close(S)),
    with_output_to(string(_), mnn_optimise:optimise_file(In, Out, Report)),
    mnn_optimise:optimise_report_line(Report, Line),
    ( exists_file(Out) -> setup_call_cleanup(open(Out, read, R), clauses(R, Emitted), close(R)), delete_file(Out) ; Emitted = none ).

clauses(R, Cs) :-
    read_term(R, T, []),
    ( T == end_of_file -> Cs = []
    ; numbervars(T, 0, _), format(string(C), "~W", [T, [quoted(true), numbervars(true), portray(false), spacing(next_argument)]]),
      Cs = [C | Rest], clauses(R, Rest) ).
io_run(s2a, [Name, Spec, Options], Result) :- with_output_to(string(_), mnn_s2a:s2a(Name, Spec, Options, Result)).

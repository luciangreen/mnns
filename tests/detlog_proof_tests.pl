:- begin_tests(mnn_detlog_proof).

:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/detlog/detlog_transform').
:- use_module('../prolog/ir/ir').

%   A program from predicate definitions: [Key-[Head-Body, ...], ...].
program(Definitions, mnn_program(sample, meta(sample, []), Predicates, proof([]), trace([]))) :-
    findall(mnn_pred(Key, [], [], Clauses, original),
            ( member(Key-Pairs, Definitions),
              findall(mnn_clause(N, Head, Body, source(sample, N)),
                      nth1(N, Pairs, Head-Body),
                      Clauses)
            ),
            Predicates).

step(Rule, proof([proof_step(1, Rule, [], equivalent(domain(all), modes(all)))])).

accepted(Rule, Before, After) :-
    program(Before, Original),
    program(After, Program),
    step(Rule, Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, Result),
    Result == accepted.

%   Runs a program in a fresh module and collects every answer of Goal, in order.
answers(Definitions, Goal, Answers) :-
    program(Definitions, mnn_program(_, _, Predicates, _, _)),
    gensym(detlog_proof_m, M),
    forall(( member(mnn_pred(_, _, _, Clauses, _), Predicates),
             member(mnn_clause(_, Head, Body, _), Clauses) ),
           ( mnn_ir:prolog_body(Body, PBody),
             assertz(M:(Head :- PBody)) )),
    findall(R, catch(( M:Goal, R = Goal ), E, R = error(E)), Answers).

same_answers(Before, After, Goals) :-
    forall(member(G, Goals),
           ( answers(Before, G, A),
             answers(After, G, B),
             assertion(A =@= B) )).

% ---- remove_green_cut

test(green_cut_removed_from_last_clause) :-
    Before = [small/1-[small(X)-conj(X < 10, !)]],
    After = [small/1-[small(Y)-(Y < 10)]],
    assertion(accepted(remove_green_cut, Before, After)),
    same_answers(Before, After, [small(5), small(20), small(10)]).

test(green_cut_with_several_goals) :-
    Before = [band/2-[band(X, low)-conj(integer(X), conj(X < 10, !))]],
    After = [band/2-[band(Y, low)-conj(integer(Y), Y < 10)]],
    assertion(accepted(remove_green_cut, Before, After)),
    same_answers(Before, After, [band(3, _), band(30, _), band(a, _)]).

test(green_cut_not_removed_from_earlier_clause, [fail]) :-
    accepted(remove_green_cut,
             [sign/2-[sign(X, neg)-conj(X < 0, !), sign(_, nonneg)-true]],
             [sign/2-[sign(Y, neg)-(Y < 0), sign(_, nonneg)-true]]).

test(green_cut_needs_a_deterministic_guard, [fail]) :-
    accepted(remove_green_cut,
             [pick/1-[pick(X)-conj(member(X, [a, b]), !)]],
             [pick/1-[pick(Y)-member(Y, [a, b])]]).

test(green_cut_not_with_a_redefined_builtin, [fail]) :-
    accepted(remove_green_cut,
             [check/1-[check(X)-conj(integer(X), !)], integer/1-[integer(_)-true, integer(_)-true]],
             [check/1-[check(Y)-integer(Y)], integer/1-[integer(_)-true, integer(_)-true]]).

% ---- compile_cut

test(cut_compiled_to_if_then_else) :-
    Before = [pick/1-[pick(X)-conj(member(X, [a, b, c]), conj(X \== a, !))]],
    After = [pick/1-[pick(Y)-ite(conj(member(Y, [a, b, c]), Y \== a), true, fail)]],
    assertion(accepted(compile_cut, Before, After)),
    same_answers(Before, After, [pick(_)]).

test(cut_compiled_keeps_earlier_clauses) :-
    Before = [first/1-[first(none)-true, first(X)-conj(member(X, [1, 2]), !)]],
    After = [first/1-[first(none)-true, first(Y)-ite(member(Y, [1, 2]), true, fail)]],
    assertion(accepted(compile_cut, Before, After)),
    same_answers(Before, After, [first(_)]).

test(cut_not_compiled_in_earlier_clause, [fail]) :-
    accepted(compile_cut,
             [p/1-[p(X)-conj(member(X, [1, 2]), !), p(3)-true]],
             [p/1-[p(Y)-ite(member(Y, [1, 2]), true, fail), p(3)-true]]).

test(cut_not_compiled_with_a_cut_in_the_guard, [fail]) :-
    accepted(compile_cut,
             [q/0-[q-conj(conj(a, !), conj(b, !))]],
             [q/0-[q-ite(conj(conj(a, !), b), true, fail)]]).

test(cut_not_compiled_with_call_in_the_guard, [fail]) :-
    accepted(compile_cut,
             [r/1-[r(G)-conj(call(G), !)]],
             [r/1-[r(H)-ite(call(H), true, fail)]]).

% ---- compile_once

test(once_compiled) :-
    Before = [first/1-[first(X)-once(member(X, [a, b, c]))]],
    After = [first/1-[first(Y)-ite(member(Y, [a, b, c]), true, fail)]],
    assertion(accepted(compile_once, Before, After)),
    same_answers(Before, After, [first(_)]).

test(once_compiled_inside_negation) :-
    Before = [none/1-[none(L)-not(once(member(x, L)))]],
    After = [none/1-[none(M)-not(ite(member(x, M), true, fail))]],
    assertion(accepted(compile_once, Before, After)),
    same_answers(Before, After, [none([a, b]), none([x]), none([])]).

test(once_not_compiled_when_once_is_redefined, [fail]) :-
    accepted(compile_once,
             [p/1-[p(X)-once(member(X, [1]))], once/1-[once(_)-true]],
             [p/1-[p(Y)-ite(member(Y, [1]), true, fail)], once/1-[once(_)-true]]).

test(once_not_compiled_with_a_cut_inside, [fail]) :-
    accepted(compile_once, [p/0-[p-once(!)]], [p/0-[p-ite(!, true, fail)]]).

test(only_one_change_per_step, [fail]) :-
    accepted(compile_once,
             [p/2-[p(X, Y)-conj(once(member(X, [1])), once(member(Y, [2])))]],
             [p/2-[p(A, B)-conj(ite(member(A, [1]), true, fail), ite(member(B, [2]), true, fail))]]).

% ---- sequences, and Detlog's own output

test(sequence_of_two_steps) :-
    program([p/2-[p(X, Y)-conj(once(member(X, [1, 2])), once(member(Y, [3, 4])))]], Original),
    program([p/2-[p(A, B)-conj(ite(member(A, [1, 2]), true, fail), ite(member(B, [3, 4]), true, fail))]], Program),
    Proof = proof([proof_step(1, compile_once, [], equivalent(domain(all), modes(all))),
                   proof_step(2, compile_once, [], equivalent(domain(all), modes(all)))]),
    mnn_proof_checker:check_proof(Program, Original, Proof, Result),
    assertion(Result == accepted).

test(detlog_transform_output_is_proved) :-
    program([small/1-[small(X)-conj(X < 10, !)],
             pick/1-[pick(Y)-conj(member(Y, [1, 2, 3]), conj(Y > 1, !))],
             first/1-[first(Z)-once(member(Z, [a, b]))]],
            Original),
    mnn_detlog_transform:transform_program(Original, Transformed,
                                           detlog_transform_report(Events)),
    findall(Rule, ( member(E, Events), event_rule(E, Rule) ), Rules),
    msort(Rules, Sorted),
    assertion(Sorted == [compile_cut, compile_once, remove_green_cut]),
    findall(proof_step(N, R, [], equivalent(domain(all), modes(all))),
            nth1(N, Rules, R), Steps),
    mnn_proof_checker:check_proof(Transformed, Original, proof(Steps), Result),
    assertion(Result == accepted).

event_rule(removed_green_cut(_, _), remove_green_cut).
event_rule(compiled_cut(_, _, _), compile_cut).
event_rule(compiled_once(_, _, _), compile_once).

:- end_tests(mnn_detlog_proof).

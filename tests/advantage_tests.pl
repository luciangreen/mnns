:- begin_tests(mnn_advantage).

:- use_module('../prolog/complexity/advantage').

test(tasks) :-
    mnn_advantage:ca_tasks(4, 1, random, Ts),
    assertion(Ts == [task(1,9,8), task(2,7,2), task(3,2,3), task(4,7,4)]).

test(makespan) :-
    mnn_advantage:ca_makespan([task(1,9,8), task(2,7,2)], [human, robot], M),
    assertion(M == 9).

test(random_six) :-
    mnn_advantage:ca_report(6, 1, random, R),
    assertion(memberchk(human_alone(34), R)),
    assertion(memberchk(robot_alone(24), R)),
    assertion(memberchk(absolute_advantage(15), R)),
    assertion(memberchk(comparative_advantage(15, cut(2)), R)),
    assertion(memberchk(optimal(13, [human,robot,human,robot,robot,robot]), R)),
    memberchk(fractional_optimum(T, shared(1)), R),
    assertion(T =:= 191 rdiv 17),
    assertion(memberchk(gains_from_trade(11), R)),
    memberchk(proof(Steps), R),
    assertion(Steps = [ step(1, optimal_exhaustive, proved(tried(64))),
                        step(2, team_beats_solo, proved),
                        step(3, duality_certificate, proved(weight(_))),
                        step(4, integer_above_fractional, proved),
                        step(5, rounding_bound, proved(within(9))),
                        step(6, ricardo, not_applicable(human_faster_somewhere)),
                        step(7, complexity, np_hard(partition)) ]),
    memberchk(step(3, _, proved(weight(L))), Steps),
    assertion(L =:= 8 rdiv 17).

test(ricardo_robot_faster_everywhere) :-
    mnn_advantage:ca_report(8, 5, robot_better, R),
    assertion(memberchk(robot_faster_at_every_task(yes), R)),
    assertion(memberchk(robot_alone(26), R)),
    assertion(memberchk(absolute_advantage(26), R)),
    assertion(memberchk(comparative_advantage(17, cut(2)), R)),
    memberchk(optimal(15, _), R),
    memberchk(fractional_optimum(T, shared(6)), R),
    assertion(T =:= 103 rdiv 7),
    memberchk(proof(Steps), R),
    assertion(memberchk(step(6, ricardo, proved(gain(11))), Steps)),
    assertion(memberchk(step(5, rounding_bound, proved(within(8))), Steps)).

test(one_task_no_gain) :-
    mnn_advantage:ca_report(1, 2, robot_better, R),
    assertion(memberchk(gains_from_trade(0), R)),
    memberchk(proof(Steps), R),
    assertion(memberchk(step(6, ricardo, proved(gain(0))), Steps)).

test(twelve_tasks) :-
    mnn_advantage:ca_report(12, 9, robot_better, R),
    assertion(memberchk(optimal(23, _), R)),
    assertion(memberchk(comparative_advantage(25, cut(3)), R)),
    assertion(memberchk(gains_from_trade(18), R)),
    memberchk(fractional_optimum(T, shared(11)), R),
    assertion(T =:= 200 rdiv 9).

:- end_tests(mnn_advantage).

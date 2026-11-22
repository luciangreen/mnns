:- begin_tests(mnn_complexity).

:- use_module('../prolog/complexity/complexity').

test(instance) :-
    mnn_complexity:cx_instance(4, 3, 7, true, I),
    assertion(I == inst([0,0,0,0], [[4,-3,2],[2,-3,-2],[-2,-3,1]])).

test(verify_linear) :-
    mnn_complexity:cx_verify([[1,2,3],[-1,2,3]], [0,0,1], R),
    assertion(R == ok(4)),
    mnn_complexity:cx_verify([[1,2,3]], [0,0,0], R2),
    assertion(R2 == rejected(3)).

test(planted_ten) :-
    mnn_complexity:cx_report(10, 43, 1, true, 5, R),
    assertion(R = [n(10), m(43), planted(true), sat(yes), robot_brute(45), robot_mnn(10),
                   human_verify(71), team(5, 2, solved), proof(_)]),
    memberchk(proof(Steps), R),
    assertion(Steps == [ step(1, planted_ok, proved), step(2, soundness, proved),
                         step(3, agreement, proved),
                         step(4, completeness, not_applicable(satisfiable)),
                         step(5, verify_linear, proved(at_most(129))),
                         step(6, team_bound, proved(at_most(32))),
                         step(7, p_vs_np, open) ]).

test(unsat_needs_everything) :-
    mnn_complexity:cx_report(8, 34, 5, false, 4, R),
    assertion(memberchk(sat(no), R)),
    assertion(memberchk(robot_brute(256), R)),
    assertion(memberchk(robot_mnn(13), R)),
    assertion(memberchk(team(4, 16, failed), R)),
    memberchk(proof(Steps), R),
    assertion(memberchk(step(4, completeness, proved(tried_all(256))), Steps)).

test(wrong_guess) :-
    mnn_complexity:cx_report(3, 13, 2, false, 1, R),
    assertion(memberchk(sat(yes), R)),
    assertion(memberchk(robot_brute(8), R)),
    assertion(memberchk(team(1, 4, failed), R)).

test(scaling) :-
    mnn_complexity:cx_scaling(12, 11, true, Rows),
    assertion(Rows == [row(2,9,1,2,10,1), row(4,17,6,4,29,2), row(6,26,6,5,29,1),
                       row(8,34,70,4,56,5), row(10,43,6,7,67,1), row(12,51,3398,14,70,54)]).

:- end_tests(mnn_complexity).

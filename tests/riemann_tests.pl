:- begin_tests(mnn_riemann).

:- use_module('../prolog/riemann/riemann').

near(X, Y) :- abs(X - Y) =< 2.0e-6.

test(mobius_values) :-
    numlist(1, 12, Ks),
    maplist(mnn_riemann:rh_mobius, Ks, Mus),
    assertion(Mus == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]).

test(mobius_identity_proved) :-
    mnn_riemann:rh_mobius_identity(200, R),
    assertion(R == proved(exhaustive(200))).

test(gram_matches_vasyunin) :-
    mnn_riemann:rh_gram(1, 1, G11), assertion(near(G11, 1.260661)),
    mnn_riemann:rh_gram(2, 3, G23), assertion(near(G23, 0.441104)),
    mnn_riemann:rh_gram(4, 6, G46), assertion(near(G46, 0.220552)),
    mnn_riemann:rh_gram(3, 2, G32), assertion(near(G32, G23)).

test(gram_scales_by_gcd) :-
    mnn_riemann:rh_gram(2, 3, A), mnn_riemann:rh_gram(4, 6, B),
    assertion(abs(A - 2 * B) < 1.0e-12).

test(target) :-
    mnn_riemann:rh_target(3, B), assertion(near(B, 0.507132)).

test(one_neuron) :-
    mnn_riemann:rh_optimal_net(1, net(optimal, [C], D2)),
    assertion(near(D2, 0.858212)),
    assertion(near(C, 0.335367)).

test(optimum_falls) :-
    mnn_riemann:rh_optimal_net(5, net(optimal, _, D5)),
    mnn_riemann:rh_optimal_net(10, net(optimal, _, D10)),
    assertion(near(D5, 0.036102)),
    assertion(near(D10, 0.023772)),
    assertion(D10 < D5).

test(manual_never_beats_optimum) :-
    forall(between(1, 12, N),
           ( mnn_riemann:rh_manual_net(N, net(manual, _, EM)),
             mnn_riemann:rh_optimal_net(N, net(optimal, _, D2)),
             EM >= D2 - 1.0e-12 )).

test(training_descends) :-
    mnn_riemann:rh_train(4, 3, R),
    memberchk(errors(Es), R),
    assertion(length(Es, 4)),
    Es = [E0, E1, E2, E3],
    assertion(near(E0, 0.214367)), assertion(near(E1, 0.094311)),
    assertion(near(E2, 0.077091)), assertion(near(E3, 0.074332)),
    assertion(memberchk(descent(proved(monotone(3))), R)).

test(report_ten) :-
    mnn_riemann:rh_report(10, R),
    memberchk(optimal_d2(D2), R), assertion(near(D2, 0.023772)),
    memberchk(manual_d2(EM), R), assertion(near(EM, 0.137186)),
    memberchk(trained_d2(ET), R), assertion(near(ET, 0.036493)),
    memberchk(c0(C0), R), assertion(near(C0, 0.046191)),
    memberchk(ratio_to_ceiling(Q), R), assertion(near(Q, 1.184998)),
    memberchk(proof(proof(Steps)), R),
    assertion(Steps == [ step(1, gram_positive_definite, proved),
                         step(2, normal_equations, proved),
                         step(3, pythagoras(manual), proved(not_below_optimum)),
                         step(4, pythagoras(trained), proved(not_below_optimum)),
                         step(5, descent, proved(monotone(10))),
                         step(6, mobius_identity, proved(exhaustive(10))) ]).

test(report_one_has_no_ceiling) :-
    mnn_riemann:rh_report(1, R),
    assertion(memberchk(c0_over_ln_n(undefined), R)).

test(ceiling_approached_from_above) :-
    mnn_riemann:rh_report(30, R),
    memberchk(ratio_to_ceiling(Q), R),
    assertion(near(Q, 1.069891)),
    assertion(Q > 1).

test(check_proof_accepts) :-
    mnn_riemann:rh_report(6, R),
    mnn_riemann:rh_check_proof(R, V),
    assertion(V == accepted).

test(check_proof_rejects_tampered) :-
    mnn_riemann:rh_report(6, R),
    select(optimal_d2(D), R, optimal_d2(D1), R1),
    D1 is D / 2,
    mnn_riemann:rh_check_proof(R1, V),
    assertion(V == rejected).

test(robin_exceptions) :-
    mnn_riemann:rh_robin(1, 5100, R),
    assertion(R == [ checked(5098),
                     exceptions([3,4,5,6,8,9,10,12,16,18,20,24,30,36,48,60,72,
                                 84,120,180,240,360,720,840,2520,5040]),
                     above_5040(none) ]).

test(robin_empty_range) :-
    mnn_riemann:rh_robin(10, 5, R),
    assertion(R == [checked(0), exceptions([]), above_5040(none)]).

test(neurons_needed) :-
    mnn_riemann:rh_neurons_needed(0.01, L1), assertion(near(L1, 2.006068)),
    mnn_riemann:rh_neurons_needed(0.001, L2), assertion(near(L2, 20.060678)).

:- end_tests(mnn_riemann).

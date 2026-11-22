:- begin_tests(mnn_riemann_hp).

:- use_module('../prolog/riemann/riemann_hp').

test(pi_digits) :-
    mnn_riemann_hp:rh_hp_constant(pi, 30, D),
    assertion(D == '3.141592653589793238462643383279').

test(gamma_digits) :-
    mnn_riemann_hp:rh_hp_constant(gamma, 30, D),
    assertion(D == '0.577215664901532860606512090082').

test(c0_digits) :-
    mnn_riemann_hp:rh_hp_constant(c0, 30, D),
    assertion(D == '0.046191417932242067628620495812').

test(gram_digits) :-
    mnn_riemann_hp:rh_hp_gram(2, 3, 30, D),
    assertion(D == '0.441103509279402176327335920469').

test(one_neuron) :-
    mnn_riemann_hp:rh_hp_report(1, 20, R),
    assertion(memberchk(optimal_d2_digits('0.85821205139551088466'), R)),
    assertion(memberchk(manual_d2(3.10623), R)).

test(ten_neurons_matches_float) :-
    mnn_riemann_hp:rh_hp_report(10, 30, R),
    assertion(memberchk(optimal_d2_digits('0.023771865556039573749669750409'), R)),
    assertion(memberchk(manual_d2(0.137186), R)),
    assertion(memberchk(trained_d2(0.036493), R)),
    assertion(memberchk(ratio_digits('1.184998116799279807633506033772'), R)),
    memberchk(proof(proof(Steps)), R),
    assertion(Steps == [ step(1, gram_positive_definite, proved),
                         step(2, normal_equations, proved),
                         step(3, pythagoras(manual), proved(not_below_optimum)),
                         step(4, pythagoras(trained), proved(not_below_optimum)),
                         step(5, descent, proved(monotone(10))),
                         step(6, mobius_identity, proved(exhaustive(10))),
                         step(7, float_cross_check, proved(agrees(1.0e-9))) ]).

test(hundred_neurons) :-
    mnn_riemann_hp:rh_hp_report(100, 40, R),
    assertion(memberchk(optimal_d2_digits('0.0101887625014779902486828617607996825844'), R)),
    assertion(memberchk(manual_d2(0.147298), R)),
    assertion(memberchk(trained_d2(0.043852), R)),
    assertion(memberchk(c0_over_ln_n(0.01003), R)),
    assertion(memberchk(ratio_digits('1.0157944355106833496687774928659503833391'), R)),
    mnn_riemann_hp:rh_hp_check_proof(R, V),
    assertion(V == accepted).

test(check_rejects_tampered) :-
    mnn_riemann_hp:rh_hp_report(6, 20, R),
    select(optimal_d2_digits(_), R, optimal_d2_digits('0.5'), R1),
    mnn_riemann_hp:rh_hp_check_proof(R1, V),
    assertion(V == rejected).

test(series) :-
    mnn_riemann_hp:rh_hp_series([10], 30, Rows),
    assertion(Rows == [row(10, 0.023772, 0.137186, 0.036493, 0.020061, 1.184998)]).

:- end_tests(mnn_riemann_hp).

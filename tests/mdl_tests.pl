:- begin_tests(mnn_mdl).

:- use_module('../prolog/thermo/mdl').
:- use_module('../prolog/s2a/s2a').
:- use_module('../prolog/s2a/s2a2_bridge').
:- use_module('../prolog/aioc/assessment').
:- use_module('../prolog/aioc/size').

% ---- description lengths ----

test(renaming_variables_keeps_the_length) :-
    mnn_mdl:term_bits([(p(X, Y) :- q(Y, X))], B1),
    mnn_mdl:term_bits([(p(A, B) :- q(B, A))], B2),
    assertion(B1 == B2).

test(parts_add_up) :-
    mnn_mdl:term_bits([f(a, b, a), g(1)], description_length(T, parts(A, L, C, R))),
    assertion(T =:= A + L + C + R),
    assertion(A > 0).

test(repetition_costs_less_than_variety) :-
    length(Same, 40), maplist(=(a), Same),
    numlist(1, 40, Different),
    mnn_mdl:term_bits(Same, description_length(S, _)),
    mnn_mdl:term_bits(Different, description_length(D, _)),
    assertion(S < D).

test(empty_input_has_one_length_bit) :-
    mnn_mdl:term_bits([], B),
    assertion(B == description_length(1, parts(0, 1, 0, 0))).

% ---- shorter than its data ----

test(rule_explains_many_examples) :-
    affine(24, Spec, Pairs),
    mnn_s2a:s2a(f, Spec, [], P),
    P = mnn_program(_, meta(s2a_affine(_, _, _), _), _, _, _),
    mnn_mdl:mdl_verdict(P, Pairs, V),
    assertion(V = explains(_, _)).

test(rule_does_not_explain_two_examples) :-
    affine(2, Spec, Pairs),
    mnn_s2a:s2a(f, Spec, [], P),
    mnn_mdl:mdl_verdict(P, Pairs, V),
    assertion(V = memorises(_, _)).

test(table_memorises) :-
    scrambled(24, Spec, Pairs),
    mnn_s2a:s2a(f, Spec, [allow_table(true)], P),
    P = mnn_program(_, meta(s2a_table(_), _), _, _, _),
    mnn_mdl:mdl_verdict(P, Pairs, V),
    assertion(V = memorises(_, _)),
    V = memorises(program_bits(PB), data_bits(DB)),
    assertion(PB > DB).

% ---- used by the S2A2 bridge ----

test(bridge_records_the_verdict) :-
    affine(24, Spec, _),
    mnn_s2a2:s2a2(f, Spec, [mdl(record)], P),
    P = mnn_program(_, _, _, _, trace(T)),
    assertion(last(T, s2a2_mdl(explains(_, _)))).

test(bridge_keeps_an_explaining_program_under_require) :-
    affine(24, Spec, _),
    mnn_s2a2:s2a2(f, Spec, [mdl(require)], P),
    assertion(P = mnn_program(_, _, _, _, _)).

test(bridge_rejects_a_memorising_program_under_require) :-
    atoms(10, Spec),
    mnn_s2a2:s2a2(f, Spec, [allow_table(true), mdl(require), ga(false), time_limit(10)], R),
    assertion(R = no_algorithm(memorises(program_bits(_), data_bits(_)))).

test(bridge_without_mdl_is_unchanged) :-
    affine(5, Spec, _),
    mnn_s2a2:s2a2(f, Spec, [], P1),
    mnn_s2a:s2a(f, Spec, [], P2),
    assertion(P1 =@= P2).

test(bad_mdl_option_is_rejected) :-
    affine(5, Spec, _),
    mnn_s2a2:s2a2(f, Spec, [mdl(always)], R),
    assertion(R == no_algorithm(invalid_options)).

% ---- used by AIOC ranking ----

test(equal_sizes_rank_by_description_length) :-
    Short = program(p, [mnn_clause(1, p(a), true, source(t, 1))]),
    Long = program(p, [mnn_clause(1, p(a_much_longer_constant_name), true, source(t, 1))]),
    maplist(as_program, [Short, Long], [S, L]),
    mnn_aioc_size:measure_program_size(S, SizeS),
    mnn_aioc_size:measure_program_size(L, SizeL),
    assertion(SizeS = SizeL),
    Cmp = size_comparison(SizeS, SizeS, weighted_delta(0), structural_effect(unchanged)),
    mnn_aioc_assessment:candidate_rank_key(ranked_candidate(a_long, L, Cmp), KL-_),
    mnn_aioc_assessment:candidate_rank_key(ranked_candidate(z_short, S, Cmp), KS-_),
    keysort([KL-a_long, KS-z_short], [_-First, _]),
    assertion(First == z_short).

% ---- helpers ----

affine(N, Spec, Pairs) :-
    numlist(1, N, Xs),
    findall([[input, [['A', X]]], [output, [['B', Y]]]],
            ( member(X, Xs), Y is 3 * X + 2 ), Spec),
    findall(pair(X, Y), ( member(X, Xs), Y is 3 * X + 2 ), Pairs).

scrambled(N, Spec, Pairs) :-
    numlist(1, N, Xs),
    findall([[input, [['A', X]]], [output, [['B', Y]]]],
            ( member(X, Xs), Y is (X * 7919 + 13) mod 101 ), Spec),
    findall(pair(X, Y), ( member(X, Xs), Y is (X * 7919 + 13) mod 101 ), Pairs).

atoms(N, Spec) :-
    numlist(1, N, Xs),
    findall([[input, [['A', I]]], [output, [['B', O]]]],
            ( member(X, Xs),
              atom_concat(in, X, I),
              Y is (X * 7 + 3) mod 11,
              atom_concat(out, Y, O) ), Spec).

as_program(program(Name, Clauses),
           mnn_program(Name, meta(t, [clause(1)]),
                       [mnn_pred(Name/1, ['?'], [any], Clauses, original)],
                       proof([]), trace([]))).

:- end_tests(mnn_mdl).

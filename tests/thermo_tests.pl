:- begin_tests(mnn_thermo).

:- use_module('../prolog/thermo/thermo').

test(banana_code) :-
    mnn_thermo:thermo_compress([b,a,n,a,n,a], Code),
    assertion(Code == thermo([a,b,n], [3,1,2], 34)).

test(banana_round_trip) :-
    mnn_thermo:thermo_decompress(thermo([a,b,n], [3,1,2], 34), S),
    assertion(S == [b,a,n,a,n,a]).

test(empty_sequence) :-
    mnn_thermo:thermo_compress([], Code),
    assertion(Code == thermo([], [], 0)),
    mnn_thermo:thermo_decompress(Code, S),
    assertion(S == []).

test(one_symbol_needs_no_rank_bits) :-
    mnn_thermo:thermo_report([1,1,1,1], R),
    assertion(memberchk(rank_bits(0), R)),
    assertion(memberchk(class_size(1), R)),
    assertion(memberchk(landauer_joules_300k(0.0), R)).

test(neurons_add_up_to_rank) :-
    mnn_thermo:thermo_neurons([m,i,s,s,i,s,s,i,p,p,i], Ns),
    assertion(Ns == [neuron(1,m,12600), neuron(2,i,0), neuron(3,s,700),
                     neuron(4,s,350), neuron(5,i,0), neuron(6,s,60),
                     neuron(7,s,24), neuron(8,i,0), neuron(9,p,1),
                     neuron(10,p,1), neuron(11,i,0)]),
    mnn_thermo:thermo_compress([m,i,s,s,i,s,s,i,p,p,i], thermo(_, _, 13736)).

test(abracadabra_report) :-
    atom_chars(abracadabra, Cs),
    mnn_thermo:thermo_report(Cs, R),
    assertion(R == [ n(11), alphabet([a,b,c,d,r]), counts([5,2,1,1,2]),
                     rank(21519), class_size(83160), rank_bits(17),
                     composition_bits(11), raw_bits(33), entropy_bits(22.444),
                     erased_bits_irreversible(5), erased_bits_reversible(0),
                     landauer_joules_300k(1.435e-20) ]).

test(rank_bits_never_exceed_entropy) :-
    atom_chars(mississippi, Cs),
    mnn_thermo:thermo_report(Cs, R),
    memberchk(rank_bits(RB), R),
    memberchk(entropy_bits(E), R),
    assertion(RB =< ceiling(E)).

test(out_of_range_rank_does_not_decode, [fail]) :-
    mnn_thermo:thermo_decompress(thermo([a,b,n], [3,1,2], 60), _).

test(unsorted_alphabet_does_not_decode, [fail]) :-
    mnn_thermo:thermo_decompress(thermo([b,a], [1,1], 0), _).

test(landauer_one_bit_at_300k) :-
    mnn_thermo:thermo_landauer(1, 300, J),
    assertion(J =:= 2.871e-21).

test(proof_over_three_symbols) :-
    mnn_thermo:thermo_prove([x,y,z], 6, P),
    assertion(P = proof([proof_step(1, thermo_round_trip, [], verified(_, count(1093))),
                         proof_step(2, thermo_bijection, [], verified(type_classes(_), ranks_exact)),
                         proof_step(3, thermo_neuron_sum, [], _),
                         proof_step(4, thermo_entropy_bound, [], _),
                         proof_step(5, thermo_landauer, [], erased_bits(0))])).

test(proof_over_four_symbols) :-
    mnn_thermo:thermo_prove([0,1,2,3], 5, P),
    assertion(P = proof([_, _, _, _, _])).

test(proof_rejects_repeated_alphabet) :-
    mnn_thermo:thermo_prove([a,a], 3, P),
    assertion(P == rejected(bad_domain, alphabet([a,a]))).

test(compress_is_deterministic) :-
    findall(C, mnn_thermo:thermo_compress([c,a,b,a], C), Cs),
    assertion(Cs = [_]).

:- end_tests(mnn_thermo).

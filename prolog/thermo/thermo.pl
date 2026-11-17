:- module(mnn_thermo,
          [ thermo_compress/2,
            thermo_decompress/2,
            thermo_neurons/2,
            thermo_report/2,
            thermo_landauer/3,
            thermo_prove/3,
            thermo_table_program/4
          ]).

/** <module> Thermodynamic compression MNN

The sharpest lossless compression an MNN can do, and what it costs in heat.

A sequence is coded as thermo(Alphabet, Counts, Rank): its sorted alphabet,
how often each symbol occurs, and its rank among all sequences with exactly
those counts (enumerative coding). For a sequence of length N with counts
c1..ck there are M = N! / (c1! ... ck!) such sequences, and the ranks of
the class are exactly 0..M-1, so the rank needs ceil(log2 M) bits. No
injective code for that class can use fewer (pigeonhole), and
log2 M =< N * H(counts), so it is never worse than the empirical entropy.

The rank is a sum of neuron weights. When the next symbol is the I-th of
the alphabet, the neuron fires with weight M * (c1 + ... + c(I-1)) / N,
where M and N belong to the counts still left. Each term M * cj / N is
the multinomial of the counts with cj lowered by one (Pascal's rule for
multinomials), so it is a whole number, and the terms for j = 1..k add up
to M: the classes of the next symbol split 0..M-1 into blocks with no gaps
or overlaps. That is why compress and decompress are inverse bijections.

Thermodynamically, the coder is a bijection on the type class: it erases
no information, so by Landauer's principle it need not give off any heat.
A coder that throws the input away after writing a shorter code erases
raw_bits - code_bits and must give off at least that many times
k_B * T * ln 2 joules. thermo_report/2 gives both figures.

thermo_prove/3 checks all of this exhaustively on a finite domain and
returns a proof term, or the first counterexample.
*/

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(error)).
:- use_module(library(pairs)).

% Boltzmann's constant in joules per kelvin (exact, SI 2019).
boltzmann(1.380649e-23).

%!  thermo_compress(+Sequence, -Code) is det.
%
%   Code = thermo(Alphabet, Counts, Rank).

thermo_compress(Seq, thermo(Alphabet, Counts, Rank)) :-
    must_be(list, Seq),
    must_be(ground, Seq),
    sort(Seq, Alphabet),
    maplist(count_in(Seq), Alphabet, Counts),
    length(Seq, N),
    multinomial(Counts, M),
    rank(Seq, Alphabet, Counts, N, M, 0, Rank).

%!  thermo_decompress(+Code, -Sequence) is det.
%
%   Fails if the rank is outside 0..M-1 or the counts do not fit the
%   alphabet, so that only codes made by thermo_compress/2 decode.

thermo_decompress(thermo(Alphabet, Counts, Rank), Seq) :-
    must_be(list, Alphabet),
    must_be(list, Counts),
    must_be(integer, Rank),
    length(Alphabet, K),
    length(Counts, K),
    sort(Alphabet, Alphabet),
    maplist(nonneg_int, Counts),
    sum_list(Counts, N),
    multinomial(Counts, M),
    Rank >= 0,
    Rank < M,
    unrank(N, M, Alphabet, Counts, Rank, Seq).

% ---- ranking ----

rank([], _, _, _, _, Rank, Rank).
rank([X|Xs], Alphabet, Counts, N, M, Rank0, Rank) :-
    index_of(Alphabet, X, 0, I),
    prefix_sum(I, Counts, 0, Prefix),
    nth0(I, Counts, C),
    Rank1 is Rank0 + M * Prefix // N,
    M1 is M * C // N,
    N1 is N - 1,
    lower(I, Counts, Counts1),
    rank(Xs, Alphabet, Counts1, N1, M1, Rank1, Rank).

unrank(N, M, Alphabet, Counts, Rank, Seq) :-
    (   N =:= 0
    ->  Rank =:= 0,
        Seq = []
    ;   choose(Alphabet, Counts, 0, 0, M, N, Rank, X, I, Offset),
        nth0(I, Counts, C),
        Rank1 is Rank - Offset,
        M1 is M * C // N,
        N1 is N - 1,
        lower(I, Counts, Counts1),
        Seq = [X|Xs],
        unrank(N1, M1, Alphabet, Counts1, Rank1, Xs)
    ).

% choose(+Alphabet, +Counts, +I0, +Acc, +M, +N, +Rank, -X, -I, -Offset):
% the symbol whose block of ranks [Offset, Offset + M*C/N) holds Rank.
choose([A|As], [C|Cs], I0, Acc, M, N, Rank, X, I, Offset) :-
    W is M * C // N,
    (   C > 0,
        Rank < Acc + W
    ->  X = A,
        I = I0,
        Offset = Acc
    ;   Acc1 is Acc + W,
        I1 is I0 + 1,
        choose(As, Cs, I1, Acc1, M, N, Rank, X, I, Offset)
    ).

% ---- neurons ----

%!  thermo_neurons(+Sequence, -Neurons) is det.
%
%   One neuron per position: neuron(Position, Symbol, Weight). The weights
%   add up to the rank thermo_compress/2 gives.

thermo_neurons(Seq, Neurons) :-
    must_be(list, Seq),
    must_be(ground, Seq),
    sort(Seq, Alphabet),
    maplist(count_in(Seq), Alphabet, Counts),
    length(Seq, N),
    multinomial(Counts, M),
    neurons(Seq, 1, Alphabet, Counts, N, M, Neurons).

neurons([], _, _, _, _, _, []).
neurons([X|Xs], P, Alphabet, Counts, N, M, [neuron(P, X, W)|Ns]) :-
    index_of(Alphabet, X, 0, I),
    prefix_sum(I, Counts, 0, Prefix),
    nth0(I, Counts, C),
    W is M * Prefix // N,
    M1 is M * C // N,
    N1 is N - 1,
    P1 is P + 1,
    lower(I, Counts, Counts1),
    neurons(Xs, P1, Alphabet, Counts1, N1, M1, Ns).

% ---- report ----

%!  thermo_report(+Sequence, -Report) is det.
%
%   Report is a list:
%     n(N), alphabet(A), counts(C), rank(R),
%     class_size(M)               sequences with these counts,
%     rank_bits(RB)               ceil(log2 M), the sharp part of the code,
%     composition_bits(CB)        ceil(log2 C(N+K-1, K-1)) for the counts,
%     raw_bits(Raw)               N * ceil(log2 K), fixed-width symbols,
%     entropy_bits(E)             N * H(counts), to 3 decimal places,
%     erased_bits_irreversible(X) max(0, Raw - RB - CB),
%     erased_bits_reversible(0),
%     landauer_joules_300k(J)     least heat for the irreversible coder.

thermo_report(Seq, Report) :-
    thermo_compress(Seq, thermo(Alphabet, Counts, Rank)),
    length(Seq, N),
    length(Alphabet, K),
    multinomial(Counts, M),
    bits_for(M, RB),
    compositions(N, K, NC),
    bits_for(NC, CB),
    bits_for(K, SymbolBits),
    Raw is N * SymbolBits,
    entropy_bits(Counts, N, E),
    Erased is max(0, Raw - RB - CB),
    thermo_landauer(Erased, 300, J),
    Report = [ n(N), alphabet(Alphabet), counts(Counts), rank(Rank),
               class_size(M), rank_bits(RB), composition_bits(CB),
               raw_bits(Raw), entropy_bits(E),
               erased_bits_irreversible(Erased), erased_bits_reversible(0),
               landauer_joules_300k(J) ].

%!  thermo_landauer(+Bits, +Kelvin, -Joules) is det.
%
%   The least heat, Bits * k_B * T * ln 2, given off by erasing Bits bits
%   at temperature T, to 4 significant figures.

thermo_landauer(Bits, T, J) :-
    must_be(nonneg, Bits),
    must_be(positive_integer, T),
    boltzmann(KB),
    J0 is Bits * KB * T * log(2),
    sig4(J0, J).

sig4(X, Y) :-
    format(atom(A), "~3e", [X]),
    atom_number(A, Y).

% ---- proof ----

%!  thermo_prove(+Alphabet, +MaxLength, -Result) is det.
%
%   Checks every sequence over Alphabet of length 0..MaxLength:
%     1. decompress(compress(S)) = S                         (round trip)
%     2. the ranks of each type class are exactly 0..M-1     (bijection,
%        so ceil(log2 M) bits is the least any injective code can use)
%     3. the neuron weights add up to the rank               (MNN form)
%     4. rank_bits =< ceil(N * H(counts))                    (entropy bound)
%   Result is proof([...]) or rejected(Check, Witness).
%   Alphabet must have 1..4 distinct ground symbols and MaxLength 0..8.

thermo_prove(Alphabet0, MaxLen, Result) :-
    must_be(list, Alphabet0),
    must_be(ground, Alphabet0),
    must_be(between(0, 8), MaxLen),
    sort(Alphabet0, Alphabet),
    length(Alphabet, K),
    length(Alphabet0, K0),
    (   K =:= K0, K >= 1, K =< 4
    ->  findall(S, ( between(0, MaxLen, L), length(S, L),
                     seq_over(S, Alphabet) ), Seqs),
        length(Seqs, Count),
        check_all(Seqs, Classes, Result0),
        (   Result0 == ok
        ->  length(Classes, NClasses),
            Result = proof([
                proof_step(1, thermo_round_trip, [],
                           verified(domain(seqs(Alphabet, MaxLen)), count(Count))),
                proof_step(2, thermo_bijection, [],
                           verified(type_classes(NClasses), ranks_exact)),
                proof_step(3, thermo_neuron_sum, [],
                           verified(domain(seqs(Alphabet, MaxLen)), count(Count))),
                proof_step(4, thermo_entropy_bound, [],
                           verified(domain(seqs(Alphabet, MaxLen)), count(Count))),
                proof_step(5, thermo_landauer, [], erased_bits(0))
            ])
        ;   Result = Result0
        )
    ;   Result = rejected(bad_domain, alphabet(Alphabet0))
    ).

check_all(Seqs, Classes, Result) :-
    (   member(S, Seqs),
        thermo_compress(S, Code),
        \+ thermo_decompress(Code, S)
    ->  Result = rejected(round_trip, S)
    ;   member(S, Seqs),
        thermo_compress(S, thermo(_, _, R)),
        thermo_neurons(S, Ns),
        neuron_sum(Ns, 0, Sum),
        Sum =\= R
    ->  Result = rejected(neuron_sum, S)
    ;   member(S, Seqs),
        thermo_report(S, Rep),
        memberchk(rank_bits(RB), Rep),
        memberchk(n(N), Rep),
        memberchk(counts(Cs), Rep),
        entropy_exact(Cs, N, H),
        RB > ceiling(H - 1.0e-9)
    ->  Result = rejected(entropy_bound, S)
    ;   findall((A-C)-R, ( member(S, Seqs), thermo_compress(S, thermo(A, C, R)) ), Pairs0),
        keysort(Pairs0, Pairs),
        group_pairs_by_key(Pairs, Classes),
        (   member((A-C)-Rs0, Classes),
            msort(Rs0, Rs),
            multinomial(C, M),
            Top is M - 1,
            numlist_or_empty(0, Top, Want),
            Rs \== Want
        ->  Result = rejected(bijection, class(A, C))
        ;   Result = ok
        )
    ).

numlist_or_empty(Lo, Hi, L) :-
    (   Hi < Lo
    ->  L = []
    ;   numlist(Lo, Hi, L)
    ).

% ---- table program ----

%!  thermo_table_program(+Name, +Alphabet, +Counts, -Program) is semidet.
%
%   The whole type class as an MNN program of facts Name(Rank, Sequence),
%   one per rank 0..M-1 in order. Pure facts run in both directions: with
%   the rank bound they decode, with the sequence bound they encode.
%   Fails unless Alphabet is sorted and distinct, Counts fit it, and the
%   class has 1..5040 members.

thermo_table_program(Name, Alphabet, Counts, Program) :-
    atom(Name),
    is_list(Alphabet),
    ground(Alphabet),
    sort(Alphabet, Alphabet),
    is_list(Counts),
    length(Alphabet, K),
    length(Counts, K),
    maplist(nonneg_int, Counts),
    multinomial(Counts, M),
    M >= 1,
    M =< 5040,
    Top is M - 1,
    numlist(0, Top, Ranks),
    maplist(table_clause(Name, Alphabet, Counts), Ranks, Clauses),
    findall(clause(Id), between(1, M, Id), Ids),
    Program = mnn_program(
                  Name, meta(thermo(Name), Ids),
                  [mnn_pred(Name/2, ['?', '?'], [any, any], Clauses, original)],
                  proof([]), trace([])).

table_clause(Name, Alphabet, Counts, Rank,
             mnn_clause(Id, Head, true, source(thermo(Name), Id))) :-
    thermo_decompress(thermo(Alphabet, Counts, Rank), Seq),
    Id is Rank + 1,
    Head =.. [Name, Rank, Seq].

% ---- arithmetic ----

multinomial(Counts, M) :-
    sum_list(Counts, N),
    factorial(N, FN),
    factorial_product(Counts, 1, Den),
    M is FN // Den.

factorial(N, F) :-
    factorial(N, 1, F).
factorial(N, A, F) :-
    (   N =< 0
    ->  F = A
    ;   A1 is A * N,
        N1 is N - 1,
        factorial(N1, A1, F)
    ).

% compositions(N, K, C): ways to write N as K counts >= 0, C(N+K-1, K-1).
compositions(N, K, C) :-
    (   K =:= 0
    ->  ( N =:= 0 -> C = 1 ; C = 0 )
    ;   compositions_(N, K, C)
    ).
compositions_(N, K, C) :-
    Top is N + K - 1,
    Bot is K - 1,
    factorial(Top, FT),
    factorial(Bot, FB),
    factorial(N, FN),
    C is FT // (FB * FN).

% bits_for(V, B): bits to tell apart V things, ceil(log2 V); 0 when V =< 1.
bits_for(V, B) :-
    (   V =< 1
    ->  B = 0
    ;   B is msb(V - 1) + 1
    ).

entropy_exact(Counts, N, H) :-
    (   N =:= 0
    ->  H = 0.0
    ;   entropy_sum(Counts, N, 0.0, H)
    ).

entropy_sum([], _, H, H).
entropy_sum([C|Cs], N, H0, H) :-
    (   C =:= 0
    ->  H1 = H0
    ;   H1 is H0 - C * log(C / N) / log(2)
    ),
    entropy_sum(Cs, N, H1, H).

entropy_bits(Counts, N, E) :-
    entropy_exact(Counts, N, H),
    E is round(H * 1000) / 1000.0.

% ---- lists ----

count_in(Seq, X, C) :-
    count_in(Seq, X, 0, C).
count_in([], _, C, C).
count_in([Y|Ys], X, C0, C) :-
    (   Y == X
    ->  C1 is C0 + 1
    ;   C1 = C0
    ),
    count_in(Ys, X, C1, C).

nonneg_int(C) :-
    integer(C),
    C >= 0.

% seq_over(?Seq, +Alphabet): Seq (of fixed length) uses only Alphabet.
seq_over([], _).
seq_over([X|Xs], Alphabet) :-
    member(X, Alphabet),
    seq_over(Xs, Alphabet).

neuron_sum([], S, S).
neuron_sum([neuron(_, _, W)|Ns], S0, S) :-
    S1 is S0 + W,
    neuron_sum(Ns, S1, S).

factorial_product([], P, P).
factorial_product([C|Cs], P0, P) :-
    factorial(C, F),
    P1 is P0 * F,
    factorial_product(Cs, P1, P).

index_of([A|As], X, I0, I) :-
    (   A == X
    ->  I = I0
    ;   I1 is I0 + 1,
        index_of(As, X, I1, I)
    ).

prefix_sum(I, Counts, Acc, Sum) :-
    (   I =:= 0
    ->  Sum = Acc
    ;   Counts = [C|Cs],
        Acc1 is Acc + C,
        I1 is I - 1,
        prefix_sum(I1, Cs, Acc1, Sum)
    ).

lower(I, [C|Cs], [C1|Cs1]) :-
    (   I =:= 0
    ->  C1 is C - 1,
        Cs1 = Cs
    ;   C1 = C,
        I1 is I - 1,
        lower(I1, Cs, Cs1)
    ).

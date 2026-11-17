# Thermodynamic compression MNN

`prolog/thermo/thermo.pl` (module `mnn_thermo`) is the sharpest lossless
compressor an MNN can be for a sequence whose symbol counts are known, and it
reports how much heat a compressor must give off by Landauer's principle.

## The code

A sequence is coded as `thermo(Alphabet, Counts, Rank)`:

- `Alphabet`: the sorted distinct symbols,
- `Counts`: how often each occurs,
- `Rank`: the sequence's place, from 0, among all sequences with exactly those
  counts, in dictionary order (enumerative coding).

```prolog
?- thermo_compress([b,a,n,a,n,a], C).
C = thermo([a,b,n], [3,1,2], 34).

?- thermo_decompress(thermo([a,b,n], [3,1,2], 34), S).
S = [b,a,n,a,n,a].
```

## Why it is the sharpest

For length N and counts c1..ck there are M = N! / (c1! ... ck!) sequences in
the class (the multinomial). The ranks of the class are exactly 0..M-1, so the
rank fits in ceil(log2 M) bits. Any code that tells the M sequences apart needs
at least that many bits (pigeonhole), so the rank cannot be shortened. And
log2 M =< N * H(counts), so it never does worse than the empirical entropy;
for short sequences it does noticeably better (banana: 6 bits, against
8.755 for the entropy).

## The neurons

The rank is a sum of one neuron per position. With M and N for the counts
still left, a position holding the I-th symbol fires with weight

    M * (c1 + ... + c(I-1)) / N

Each M * cj / N is the multinomial of the counts with cj lowered by one
(Pascal's rule for multinomials), so every weight is a whole number, and the
k blocks of sizes M * cj / N add up to M with no gaps or overlaps. This is the
closed form that makes `thermo_compress/2` and `thermo_decompress/2` inverse
bijections, with only one multiply and one divide per position.

```prolog
?- thermo_neurons([b,a,n,a,n,a], Ns).
Ns = [neuron(1,b,30), neuron(2,a,0), neuron(3,n,3),
      neuron(4,a,0), neuron(5,n,1), neuron(6,a,0)].   % 30+3+1 = 34
```

## Heat

Erasing a bit gives off at least k_B T ln 2 joules (Landauer). The coder is a
bijection on the class, so it erases nothing and needs no heat. A coder that
writes the shorter code and then throws away the input erases
raw_bits - rank_bits - composition_bits bits, where raw_bits is N fixed-width
symbols and composition_bits = ceil(log2 C(N+k-1, k-1)) codes the counts
(the alphabet is taken as shared).

```prolog
?- atom_chars(abracadabra, Cs), thermo_report(Cs, R).
R = [n(11), alphabet([a,b,c,d,r]), counts([5,2,1,1,2]), rank(21519),
     class_size(83160), rank_bits(17), composition_bits(11), raw_bits(33),
     entropy_bits(22.444), erased_bits_irreversible(5),
     erased_bits_reversible(0), landauer_joules_300k(1.435e-20)].
```

For sequences of a few symbols the counts cost about as many bits as the
rank saves, so a coder that erases the input needs to erase little or nothing
(all 25 `thermo_report` cases in `io/ios.txt` give 0.0 J). The bound grows
with length: abracadabra already erases 5 bits.

`thermo_landauer(Bits, Kelvin, Joules)` gives the bound for any number of bits
and temperature, to 4 significant figures.

## Proof

`thermo_prove(Alphabet, MaxLength, Result)` checks every sequence over an
alphabet of 1 to 4 symbols, of length 0 to MaxLength (at most 8), and gives

```prolog
proof([ proof_step(1, thermo_round_trip, [], verified(domain(seqs(A, L)), count(N))),
        proof_step(2, thermo_bijection, [], verified(type_classes(T), ranks_exact)),
        proof_step(3, thermo_neuron_sum, [], verified(domain(seqs(A, L)), count(N))),
        proof_step(4, thermo_entropy_bound, [], verified(domain(seqs(A, L)), count(N))),
        proof_step(5, thermo_landauer, [], erased_bits(0)) ])
```

or `rejected(Check, Witness)` with the first sequence or class that fails:

1. decoding the code gives the sequence back,
2. the ranks of every class are exactly 0..M-1 (so the code is a bijection and
   as short as possible),
3. the neuron weights add up to the rank,
4. rank_bits =< ceil(N * H(counts)),
5. so no bit is erased.

The general argument is the Pascal's-rule identity above; the check confirms
it, and the code, on the whole finite domain.

## Tests and examples

```sh
swipl -q -g "load_files('tests/thermo_tests.pl'), run_tests(mnn_thermo), halt"
```

`thermo_report` and `thermo_round_trip` are two of the cases in
`io/ios.txt`, the repository's 200 recorded inputs and outputs.

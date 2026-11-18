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

That check covers a finite domain. The next section proves it for every
length.

## Unbounded proof by induction

`prolog/thermo/thermo_induction.pl` (module `mnn_thermo_induction`) gives a
9-step proof, `thermo_induction_proof/1`, and a checker,
`thermo_check_induction(Proof, Result)`, which returns `accepted` or
`rejected(Step, Reason)` for the first step that fails.

The argument, by induction on the length N:

- **Base (N = 0).** The only count vector is all zeros, m = 0!/(0!...0!) = 1,
  and the one sequence, [], has rank 0.
- **Pascal term.** For cj >= 1, m(c - e_j) * N = m(c) * cj. So each weight
  m(c) * cj / N is the class size of a shorter class, a whole number.
- **Pascal sum.** The sum over j of m(c) * cj / N is m(c), because the cj add
  up to N.
- **Zero block.** A symbol with cj = 0 gets a block of size 0.
- **Offsets.** The code adds m(c) * (c1 + ... + c(j-1)) / N when the first
  symbol is the j-th, which is where block j starts.
- **Step.** A sequence starting with symbol j is that offset plus the rank of
  its tail, and by the induction hypothesis the tails are a bijection onto
  [0, m(c - e_j)). The blocks follow each other from 0 with no gaps or
  overlaps and end at m(c), so the class maps one-to-one onto [0, m(c)).
- **So** for every N and every count vector the coder is a bijection;
  decoding (which picks the one block that holds the rank) is its inverse;
  and ceil(log2 m(c)) bits is the least any code for the class can use.

How each step is checked:

- **Algebra** (Pascal term, Pascal sum, zero block, base): both sides are
  normalised to a product of powers of symbolic factors (n, cj, rest,
  fact(n-1), fact(cj-1), ...), using only the rewrite rules the step lists:
  the definition of m, X! = X * (X-1)! for X >= 1, 0! = 1, linearity of the
  sum, and the sum of the cj being N. No numbers are substituted, so a step
  that passes holds for all N and c. Drop a rule it needs, or change either
  side, and the step is rejected.
- **Code** (the base, offsets and decoding): the checker reads the clauses of
  `rank/7`, `choose/10` and `unrank/6` in `mnn_thermo` and checks they are,
  up to variable names, the clauses the proof is about. Change the coder and
  the proof stops checking.
- **Structure** (step, induction, inverse, minimal bits): fixed rule
  applications. The checker checks each cites accepted earlier steps of the
  right rules and states the expected conclusion. The interval and
  pigeonhole reasoning behind them is the argument above; it is not
  derived by the checker.

## AIOC incorporation

`prolog/aioc/thermo.pl` (module `mnn_aioc_thermo`) turns a whole type class
into a proof-checked MNN program:

```prolog
?- incorporate_thermo(banana, [a,b,n], [3,1,2], Program, Proof).
```

`Program` has 60 facts `banana(Rank, Sequence)`, one per rank in order
(`banana(34, [b,a,n,a,n,a])` among them). Pure facts run both ways:
`banana(34, S)` decodes and `banana(R, [b,a,n,a,n,a])` encodes. `Proof` has
two steps:

```prolog
proof([ proof_step(1, incorporate_thermo, [],
                   equivalent(domain(type_class([a,b,n], [3,1,2])), modes(all))),
        proof_step(2, thermo_induction, [], InductionProof) ])
```

`mnn_proof_checker:check_proof/4` accepts it for the source term
`thermo_source(Name, Alphabet, Counts)` only if the induction proof checks and
the program is exactly the table the coder gives (it builds the table again
and compares). Swap two facts, or leave out step 2, and it is rejected.
Classes of up to 5040 sequences can be incorporated. Because the checker
accepts it, the program can be stored in the AIOC library with
`store_entry/2`, like any other proved entry.

## Minimum description length

`prolog/thermo/mdl.pl` (module `mnn_mdl`) uses the coder to measure how many
bits a program, or a set of examples, takes to describe:

- **alphabet bits:** each distinct token spelled out, 8 bits a character plus
  an 8-bit terminator,
- **length bits:** the number of tokens, in Elias gamma code,
- **composition bits:** how often each token occurs,
- **rank bits:** which sequence with those counts.

Tokens are the terms in prefix order (`Name/Arity`, atoms, numbers, and one
token per distinct variable of a clause), so renaming variables changes
nothing. `term_bits/2`, `program_bits/2` and `data_bits/2` return
`description_length(Total, parts(Alphabet, Length, Composition, Rank))`.

`mdl_verdict(Program, Pairs, Verdict)` is the "shorter than its data" test:
`explains(program_bits(P), data_bits(D))` when the program is shorter than the
pairs it reproduces, else `memorises(...)`. A table of the pairs always
memorises. A rule needs enough examples to pay for itself: f(X) = 3X + 2
memorises 2 examples and explains 24.

It is used in two places:

- **S2A2 bridge.** `s2a2/4` takes `mdl(record)`, which adds
  `s2a2_mdl(Verdict)` to the program's trace, or `mdl(require)`, which also
  returns `no_algorithm(memorises(...))` instead of a program that memorises
  its examples. Without the option nothing changes.
- **AIOC ranking.** `rank_candidates/3` and `rank_library/2` rank by weighted
  size as before, and break ties by description length, so of two proved
  candidates of equal size the shorter description comes first.

The `mdl` case in `io/ios.txt` runs s2a on affine and scrambled examples of 2
to 24 pairs and records what it found and the verdict.

## Tests and examples

```sh
swipl -q -g "load_files('tests/thermo_tests.pl'), run_tests(mnn_thermo), halt"
swipl -q -g "load_files('tests/thermo_induction_tests.pl'), run_tests(mnn_thermo_induction), halt"
swipl -q -g "load_files('tests/mdl_tests.pl'), run_tests(mnn_mdl), halt"
```

`thermo_report`, `thermo_round_trip`, `thermo_incorporate` and `mdl` are four of the cases in
`io/ios.txt`, the repository's 200 recorded inputs and outputs.

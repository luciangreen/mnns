:- module(mnn_thermo_induction,
          [ thermo_induction_proof/1,
            thermo_check_induction/2
          ]).

/** <module> Unbounded proof that the thermo coder is a bijection

thermo_prove/3 in thermo.pl checks the coder on every sequence of a finite
domain. This module proves it for every length and every alphabet, by
induction on the length N, and checks the proof.

Notation, for a type class with counts c = (c1..ck), N = c1 + ... + ck:

    m(c)          = N! / (c1! ... ck!)       the class size
    m(c_minus_j)  = (N-1)! / (c1! ... (cj-1)! ... ck!)
    rest          = the product of ci! for i =/= j

The proof has three kinds of step, and the checker treats each differently:

  * Algebra (pascal_term, pascal_sum, zero_block, the base case): the
    conclusion is an equation, and the checker normalises both sides to a
    product of powers of symbolic factors (n, cj, rest, fact(n-1),
    fact(cj-1), ...), using only the rewrite rules the step lists as
    premises (the definition of m, fact(X) = X * fact(X-1) for X >= 1,
    0! = 1, linearity of the sum over j, and the sum of the cj being N).
    The two sides must normalise to the same product. Nothing is checked on
    numbers, so the equation holds for every N and every count vector.

  * Code (code(rank_nil), code(rank_cons), code(choose)): the checker reads
    the clauses of mnn_thermo and checks that they are, up to variable
    names, the clauses the proof is about. Change the coder and the proof
    is rejected.

  * Structure (induction_step, induction, decode_inverse, minimal_bits):
    fixed rule applications. The checker checks that each cites accepted
    earlier steps of the right rules and draws the stated conclusion. The
    reasoning they stand for (consecutive blocks of sizes w1..wk starting
    at 0 split [0, w1+...+wk) into disjoint parts; a bijection on a set of
    M things needs ceil(log2 M) bits) is set out in docs/thermo.md.
*/

:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(thermo, []).

%!  thermo_induction_proof(-Proof) is det.

thermo_induction_proof(proof([
    proof_step(1, pascal_term, [def(m), fact_rec(n), fact_rec(cj)],
               forall([c, j], implies(and(n >= 1, cj >= 1),
                                      eq(m(c_minus_j) * n, m(c) * cj)))),
    proof_step(2, pascal_sum, [linearity, def(n)],
               forall([c], implies(n >= 1,
                                   eq(sum_j(m(c) * cj / n), m(c))))),
    proof_step(3, zero_block, [],
               forall([c, j], implies(cj =:= 0, eq(m(c) * 0 / n, 0)))),
    proof_step(4, base_case, [def(m_zeros), fact_zero, code(rank_nil)],
               forall([c], implies(n =:= 0,
                                   and(eq(m(zeros), 1),
                                       bijection(rank, class(c),
                                                 interval(0, m(c))))))),
    proof_step(5, block_offsets, [step(1), code(rank_cons)],
               forall([c, j], eq(offset(j), m(c) * prefix(j) / n))),
    proof_step(6, induction_step, [step(1), step(2), step(3), step(5), ih],
               forall([c], implies(n >= 1,
                                   bijection(rank, class(c),
                                             interval(0, m(c)))))),
    proof_step(7, induction, [step(4), step(6)],
               forall([c], bijection(rank, class(c), interval(0, m(c))))),
    proof_step(8, decode_inverse, [step(7), code(choose)],
               forall([c], inverse(unrank, rank, class(c)))),
    proof_step(9, minimal_bits, [step(7)],
               forall([c], minimal(rank_bits, ceil_log2(m(c)))))
])).

%!  thermo_check_induction(+Proof, -Result) is det.
%
%   Result is accepted, or rejected(Step, Reason) for the first step that
%   does not check.

thermo_check_induction(Proof, Result) :-
    (   nonvar(Proof),
        Proof = proof(Steps),
        is_list(Steps),
        Steps \== []
    ->  check_steps(Steps, 1, [], Result)
    ;   Result = rejected(0, not_a_proof)
    ).

check_steps([], _, Accepted, Result) :-
    (   memberchk(7-induction, Accepted),
        memberchk(8-decode_inverse, Accepted),
        memberchk(9-minimal_bits, Accepted)
    ->  Result = accepted
    ;   Result = rejected(end, missing_conclusion)
    ).
check_steps([Step|Steps], Expected, Accepted, Result) :-
    (   ground(Step),
        Step = proof_step(Id, Rule, Premises, Conclusion),
        Id == Expected
    ->  (   check_step(Rule, Premises, Conclusion, Accepted)
        ->  Next is Expected + 1,
            check_steps(Steps, Next, [Id-Rule|Accepted], Result)
        ;   Result = rejected(Id, Rule)
        )
    ;   Result = rejected(Expected, malformed_step)
    ).

% ---- algebra ----

check_step(pascal_term, Premises, Conclusion, _) :-
    Conclusion = forall([c, j], implies(and(n >= 1, cj >= 1), eq(L, R))),
    algebra_rules(Premises),
    same_value(L, R, Premises).
check_step(pascal_sum, Premises, Conclusion, _) :-
    Conclusion = forall([c], implies(n >= 1, eq(sum_j(Term), R))),
    algebra_rules(Premises),
    memberchk(linearity, Premises),
    memberchk(def(n), Premises),
    sum_over_j(Term, Premises, LeftValue),
    normal(R, Premises, RightValue),
    LeftValue == RightValue.
check_step(zero_block, Premises, Conclusion, _) :-
    Conclusion = forall([c, j], implies(cj =:= 0, eq(L, R))),
    algebra_rules(Premises),
    same_value(L, R, Premises).
check_step(base_case, Premises, Conclusion, _) :-
    Premises = [def(m_zeros), fact_zero, code(rank_nil)],
    Conclusion = forall([c], implies(n =:= 0,
                                     and(eq(L, R),
                                         bijection(rank, class(c),
                                                   interval(0, m(c)))))),
    same_value(L, R, Premises),
    code_matches(rank_nil),
    % the one sequence of length 0 codes to rank 0 of a class of size 1
    mnn_thermo:thermo_compress([], thermo([], [], 0)).

% ---- code ----

check_step(block_offsets, [step(1), code(rank_cons)], Conclusion, Accepted) :-
    Conclusion == forall([c, j], eq(offset(j), m(c) * prefix(j) / n)),
    memberchk(1-pascal_term, Accepted),
    code_matches(rank_cons).

% ---- structure ----

check_step(induction_step, [step(1), step(2), step(3), step(5), ih],
           Conclusion, Accepted) :-
    Conclusion == forall([c], implies(n >= 1,
                                      bijection(rank, class(c),
                                                interval(0, m(c))))),
    memberchk(1-pascal_term, Accepted),
    memberchk(2-pascal_sum, Accepted),
    memberchk(3-zero_block, Accepted),
    memberchk(5-block_offsets, Accepted).
check_step(induction, [step(4), step(6)], Conclusion, Accepted) :-
    Conclusion == forall([c], bijection(rank, class(c), interval(0, m(c)))),
    memberchk(4-base_case, Accepted),
    memberchk(6-induction_step, Accepted).
check_step(decode_inverse, [step(7), code(choose)], Conclusion, Accepted) :-
    Conclusion == forall([c], inverse(unrank, rank, class(c))),
    memberchk(7-induction, Accepted),
    code_matches(choose),
    code_matches(unrank).
check_step(minimal_bits, [step(7)], Conclusion, Accepted) :-
    Conclusion == forall([c], minimal(rank_bits, ceil_log2(m(c)))),
    memberchk(7-induction, Accepted).

algebra_rules(Premises) :-
    is_list(Premises),
    maplist(algebra_rule, Premises).

algebra_rule(def(m)).
algebra_rule(def(m_zeros)).
algebra_rule(def(n)).
algebra_rule(fact_rec(n)).
algebra_rule(fact_rec(cj)).
algebra_rule(fact_zero).
algebra_rule(linearity).
algebra_rule(code(rank_nil)).

same_value(L, R, Rules) :-
    normal(L, Rules, VL),
    normal(R, Rules, VR),
    VL == VR.

% normal(+Expression, +Rules, -Value): Value is v(Coefficient, Factors),
% Factors a sorted list of Factor-Exponent with no zero exponents, and
% v(0, []) for zero. Coefficients stay integers; dividing needs a
% coefficient of 1 or -1.

normal(E, _, v(E, [])) :-
    integer(E),
    !.
normal(A * B, Rules, V) :-
    !,
    normal(A, Rules, VA),
    normal(B, Rules, VB),
    times(VA, VB, V).
normal(A / B, Rules, V) :-
    !,
    normal(A, Rules, VA),
    normal(B, Rules, VB),
    inverse(VB, IB),
    times(VA, IB, V).
normal(pow(E, k), Rules, V) :-
    !,
    normal(E, Rules, VE),
    VE == v(1, []),
    V = v(1, []).
normal(m(c), Rules, V) :-
    memberchk(def(m), Rules),
    !,
    normal(fact(n) / (rest * fact(cj)), Rules, V).
normal(m(c_minus_j), Rules, V) :-
    memberchk(def(m), Rules),
    !,
    normal(fact(n - 1) / (rest * fact(cj - 1)), Rules, V).
normal(m(zeros), Rules, V) :-
    memberchk(def(m_zeros), Rules),
    !,
    normal(fact(0) / pow(fact(0), k), Rules, V).
normal(fact(0), Rules, V) :-
    memberchk(fact_zero, Rules),
    !,
    V = v(1, []).
normal(fact(n), Rules, V) :-
    memberchk(fact_rec(n), Rules),
    !,
    normal(n * fact(n - 1), Rules, V).
normal(fact(cj), Rules, V) :-
    memberchk(fact_rec(cj), Rules),
    !,
    normal(cj * fact(cj - 1), Rules, V).
normal(Atom, _, v(1, [Atom-1])) :-
    symbolic_factor(Atom).

% Factors that are positive whenever the step's side condition holds.
symbolic_factor(n).
symbolic_factor(cj).
symbolic_factor(rest).
symbolic_factor(m(c)).
symbolic_factor(m(c_minus_j)).
symbolic_factor(m(zeros)).
symbolic_factor(fact(n)).
symbolic_factor(fact(n - 1)).
symbolic_factor(fact(cj)).
symbolic_factor(fact(cj - 1)).
symbolic_factor(fact(0)).

times(v(CA, FA), v(CB, FB), V) :-
    C is CA * CB,
    (   C =:= 0
    ->  V = v(0, [])
    ;   append(FA, FB, F0),
        msort(F0, F1),
        merge_exponents(F1, F),
        V = v(C, F)
    ).

inverse(v(C, F), v(C, FI)) :-
    (C =:= 1 ; C =:= -1),
    !,
    maplist(negate_exponent, F, FI).

negate_exponent(X-E, X-NE) :-
    NE is -E.

merge_exponents([], []).
merge_exponents([X-E|Rest], Merged) :-
    same_factor(Rest, X, E, Total, Others),
    (   Total =:= 0
    ->  Merged = Merged1
    ;   Merged = [X-Total|Merged1]
    ),
    merge_exponents(Others, Merged1).

same_factor([Y-E|Rest], X, E0, Total, Others) :-
    Y == X,
    !,
    E1 is E0 + E,
    same_factor(Rest, X, E1, Total, Others).
same_factor(Rest, _, Total, Total, Rest).

% sum_over_j(+Term, +Rules, -Value): the sum over j of Term. Linearity
% takes the factors that do not depend on j outside the sum; what is left
% must be exactly cj, whose sum over j is n (def(n)).
sum_over_j(Term, Rules, Value) :-
    normal(Term, Rules, v(C, Factors)),
    partition(depends_on_j, Factors, Dependent, Independent),
    Dependent == [cj-1],
    times(v(C, Independent), v(1, [n-1]), Value).

depends_on_j(X-_) :-
    memberchk(X, [cj, fact(cj), fact(cj - 1), m(c_minus_j), rest]).

% ---- the clauses the proof is about ----

code_matches(Which) :-
    code_template(Which, Head, Body),
    functor(Head, Name, Arity),
    functor(Probe, Name, Arity),
    findall((Probe :- B), clause(mnn_thermo:Probe, B), Clauses),
    member(Clause, Clauses),
    Clause =@= (Head :- Body),
    !.

code_template(rank_nil, rank([], _, _, _, _, Rank, Rank), true).
code_template(rank_cons,
    rank([X|Xs], Alphabet, Counts, N, M, Rank0, Rank),
    ( index_of(Alphabet, X, 0, I),
      prefix_sum(I, Counts, 0, Prefix),
      nth0(I, Counts, C),
      Rank1 is Rank0 + M * Prefix // N,
      M1 is M * C // N,
      N1 is N - 1,
      lower(I, Counts, Counts1),
      rank(Xs, Alphabet, Counts1, N1, M1, Rank1, Rank) )).
code_template(choose,
    choose([A|As], [C|Cs], I0, Acc, M, N, Rank, X, I, Offset),
    ( W is M * C // N,
      (   C > 0,
          Rank < Acc + W
      ->  X = A,
          I = I0,
          Offset = Acc
      ;   Acc1 is Acc + W,
          I1 is I0 + 1,
          choose(As, Cs, I1, Acc1, M, N, Rank, X, I, Offset)
      ) )).
code_template(unrank,
    unrank(N, M, Alphabet, Counts, Rank, Seq),
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
    )).

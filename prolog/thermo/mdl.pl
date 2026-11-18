:- module(mnn_mdl,
          [ term_bits/2,
            program_bits/2,
            data_bits/2,
            mdl_verdict/3
          ]).

/** <module> Minimum description length with the thermo coder

The description length of a term (a program, or a set of input/output
pairs) in bits is what it costs to send it with the thermo coder:

    alphabet bits     each distinct token spelled out, 8 bits a character
                      plus an 8-bit terminator
    length bits       the number of tokens N, Elias gamma: 2*floor(log2(N+1))+1
    composition bits  how often each token occurs, ceil(log2 C(N+K-1, K-1))
    rank bits         which sequence with those counts, ceil(log2 M)

Tokens are the term read in prefix order: Name/Arity for a compound, the
atom or number itself, and one token for each distinct variable of a clause,
so renaming variables does not change the length. Each clause ends in a
'.' token.

mdl_verdict(Program, Pairs, Verdict) is the "shorter than its data" test:
a program that reproduces the pairs explains them when it is shorter than
the pairs themselves, and memorises them otherwise (a table of the pairs is
always longer than the pairs).
*/

:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(error)).
:- use_module(thermo, []).
:- use_module('../ir/ir', []).

%!  term_bits(+Terms, -Bits) is det.
%
%   Bits = description_length(Total, parts(Alphabet, Length, Composition, Rank))
%   for the list of terms (each one a clause, or one datum).

term_bits(Terms, description_length(Total, parts(AB, LB, CB, RB))) :-
    must_be(list, Terms),
    tokens_of_terms(Terms, Tokens),
    msort(Tokens, Sorted),
    clumped(Sorted, Clumps),
    pairs_keys_values(Clumps, Alphabet, Counts),
    foldl(add_token_bits, Alphabet, 0, AB),
    length(Tokens, N),
    gamma_bits(N, LB),
    mnn_thermo:thermo_class_bits(Counts, RB, CB),
    Total is AB + LB + CB + RB.

%!  program_bits(+Program, -Bits) is det.
%
%   The description length of an mnn_program's clauses (directives included).

program_bits(Program, Bits) :-
    program_terms(Program, Terms),
    term_bits(Terms, Bits).

program_terms(Program, Terms) :-
    (   catch(once(mnn_ir:ir_to_prolog(Program, Terms0)), _, fail)
    ->  Terms = Terms0
    ;   Program = mnn_program(_, _, Predicates, _, _),
        findall((H :- B),
                ( member(mnn_pred(_, _, _, Clauses, _), Predicates),
                  member(mnn_clause(_, H, B, _), Clauses) ),
                Terms)
    ).

%!  data_bits(+Pairs, -Bits) is det.
%
%   The description length of input/output pairs, pair(In, Out) or In-Out.

data_bits(Pairs, Bits) :-
    must_be(list, Pairs),
    maplist(pair_term, Pairs, Terms),
    term_bits(Terms, Bits).

%!  mdl_verdict(+Program, +Pairs, -Verdict) is det.
%
%   Verdict is explains(program_bits(P), data_bits(D)) when P < D, else
%   memorises(program_bits(P), data_bits(D)).

mdl_verdict(Program, Pairs, Verdict) :-
    program_bits(Program, description_length(P, _)),
    data_bits(Pairs, description_length(D, _)),
    (   P < D
    ->  Verdict = explains(program_bits(P), data_bits(D))
    ;   Verdict = memorises(program_bits(P), data_bits(D))
    ).

pair_term(pair(I, O), pair(I, O)) :- !.
pair_term(I-O, pair(I, O)) :- !.
pair_term(T, _) :-
    type_error(pair, T).

% ---- tokens ----

tokens_of_terms([], []).
tokens_of_terms([T|Ts], Tokens) :-
    copy_term(T, C),
    term_variables(C, Vs),
    number_vars(Vs, 1),
    tokens(C, Tokens, ['.'|Rest]),
    tokens_of_terms(Ts, Rest).

number_vars([], _).
number_vars(['$mdl_var'(I)|Vs], I) :-
    I1 is I + 1,
    number_vars(Vs, I1).

tokens('$mdl_var'(I), ['$mdl_var'(I)|T], T) :-
    integer(I),
    !.
tokens(X, [X|T], T) :-
    atomic(X),
    !.
tokens(X, [F/N|T0], T) :-
    compound_name_arity(X, F, N),
    X =.. [_|Args],
    tokens_list(Args, T0, T).

tokens_list([], T, T).
tokens_list([A|As], T0, T) :-
    tokens(A, T0, T1),
    tokens_list(As, T1, T).

% ---- bits ----

add_token_bits(Token, B0, B) :-
    token_chars(Token, L),
    B is B0 + 8 * (L + 1).

token_chars('$mdl_var'(_), 1) :- !.
token_chars(F/N, L) :-
    !,
    token_chars(F, LF),
    L is LF + 1 + N // 256.
token_chars(X, L) :-
    format(atom(A), "~q", [X]),
    atom_length(A, L).

gamma_bits(N, B) :-
    (   N =:= 0
    ->  B = 1
    ;   B is 2 * msb(N + 1) + 1
    ).

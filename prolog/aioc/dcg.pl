:- module(mnn_aioc_dcg,
          [ incorporate_dcg/4
          ]).

:- use_module(library(error)).
:- use_module('../aioc/cfg', []).
:- use_module('../proof/proof_checker').

incorporate_dcg(Name, DCG, Program, Proof) :-
    must_be(atom, Name),
    Source = dcg_source(Name, DCG),
    (   valid_dcg_source(Name, DCG, Grammar)
    ->  mnn_aioc_cfg:build_dcg_program(Name, Grammar, Program),
        dcg_incorporation_proof(Proof),
        mnn_proof_checker:check_proof(Program, Source, Proof, accepted)
    ;   throw(error(domain_error(dcg_source, Source), _))
    ).

valid_dcg_source(Name, dcg(Start, Clauses), cfg(Start, Rules)) :-
    atom(Name),
    ground(dcg(Start, Clauses)),
    acyclic_term(dcg(Start, Clauses)),
    atom(Start),
    is_list(Clauses),
    Clauses = [_|_],
    maplist(dcg_clause_rules, Clauses, RuleGroups),
    append(RuleGroups, Rules),
    mnn_aioc_cfg:valid_cfg_source(Name, cfg(Start, Rules)).

dcg_clause_rules((Head --> Body), Rules) :-
    atom(Head),
    dcg_body_alternatives(Body, Alternatives),
    maplist(dcg_alternative_rule(Head), Alternatives, Rules).

dcg_alternative_rule(Head, Symbols, rule(Head, Symbols)).

dcg_body_alternatives(Body, Alternatives) :-
    (   Body = (Left ; Right)
    ->  dcg_body_alternatives(Left, LeftAlternatives),
        dcg_body_alternatives(Right, RightAlternatives),
        append(LeftAlternatives, RightAlternatives, Alternatives)
    ;   Body = (Left, Right)
    ->  dcg_body_alternatives(Left, LeftAlternatives),
        dcg_body_alternatives(Right, RightAlternatives),
        append_alternatives(LeftAlternatives, RightAlternatives,
                            Alternatives)
    ;   Body == []
    ->  Alternatives = [[]]
    ;   is_list(Body)
    ->  maplist(dcg_terminal, Body, Symbols),
        Alternatives = [Symbols]
    ;   atom(Body)
    ->  Alternatives = [[nonterminal(Body)]]
    ).

dcg_terminal(Token, terminal(Token)) :-
    ground(Token),
    acyclic_term(Token).

append_alternatives([], _, []).
append_alternatives([Left|Lefts], Rights, Alternatives) :-
    append_alternatives_for(Left, Rights, First),
    append_alternatives(Lefts, Rights, Rest),
    append(First, Rest, Alternatives).

append_alternatives_for(_, [], []).
append_alternatives_for(Left, [Right|Rights], [Combined|Rest]) :-
    append(Left, Right, Combined),
    append_alternatives_for(Left, Rights, Rest).

dcg_incorporation_proof(
    proof([proof_step(1, incorporate_dcg, [],
                      equivalent(domain(all), modes(all)))])).

:- module(mnn_aioc_cfg,
          [ incorporate_cfg/4,
            incorporate_dcg/4
          ]).

:- use_module(library(error)).
:- use_module('../proof/proof_checker').

incorporate_cfg(Name, Grammar, Program, Proof) :-
    must_be(atom, Name),
    (   valid_cfg(Grammar)
    ->  Grammar = cfg(Start, Rules),
        build_grammar_program(cfg, Name, Start, Rules, Program),
        grammar_proof(incorporate_cfg, Proof),
        mnn_proof_checker:check_proof(
            Program, cfg_source(Name, Grammar), Proof, accepted)
    ;   throw(error(domain_error(cfg_grammar, Grammar), _))
    ).

incorporate_dcg(Name, Grammar, Program, Proof) :-
    must_be(atom, Name),
    (   valid_dcg(Grammar)
    ->  Grammar = dcg(Start, DcgRules),
        dcg_rules(DcgRules, Rules),
        build_grammar_program(dcg, Name, Start, Rules, Program),
        grammar_proof(incorporate_dcg, Proof),
        mnn_proof_checker:check_proof(
            Program, dcg_source(Name, Grammar), Proof, accepted)
    ;   throw(error(domain_error(dcg_grammar, Grammar), _))
    ).

valid_cfg(cfg(Start, Rules)) :-
    valid_grammar(Start, Rules).

valid_dcg(dcg(Start, DcgRules)) :-
    is_list(DcgRules),
    maplist(valid_dcg_rule, DcgRules),
    dcg_rules(DcgRules, Rules),
    valid_grammar(Start, Rules).

valid_dcg_rule(dcg_rule(Name, Symbols)) :-
    valid_nonterminal_name(Name),
    is_list(Symbols),
    maplist(valid_symbol, Symbols).

valid_grammar(Start, Rules) :-
    atom(Start),
    is_list(Rules),
    Rules = [_|_],
    maplist(valid_cfg_rule, Rules),
    rule_names(Rules, Names),
    memberchk(Start, Names),
    maplist(references_defined(Names), Rules).

valid_cfg_rule(rule(Name, Symbols)) :-
    valid_nonterminal_name(Name),
    is_list(Symbols),
    maplist(valid_symbol, Symbols).

valid_symbol(terminal(Token)) :-
    ground(Token),
    acyclic_term(Token).
valid_symbol(nonterminal(Name)) :-
    atom(Name).

valid_nonterminal_name(Name) :-
    atom(Name),
    Name \== '.',
    Head =.. [Name, _, _],
    \+ predicate_property(system:Head, built_in).

references_defined(Names, rule(_, Symbols)) :-
    maplist(reference_defined(Names), Symbols).

reference_defined(Names, nonterminal(Name)) :-
    memberchk(Name, Names).
reference_defined(_, terminal(_)).

rule_names([], []).
rule_names([rule(Name, _)|Rules], [Name|Names]) :-
    rule_names(Rules, Names).

dcg_rules([], []).
dcg_rules([dcg_rule(Name, Symbols)|DcgRules], [rule(Name, Symbols)|Rules]) :-
    dcg_rules(DcgRules, Rules).

build_grammar_program(Kind, Name, Start, Rules, Program) :-
    rule_names(Rules, RuleNames),
    ordered_unique(RuleNames, [], Names),
    grammar_predicates(Names, Rules, Kind, Name, Predicates),
    length(Rules, RuleCount),
    numlist(1, RuleCount, RuleIds),
    maplist(clause_event, RuleIds, Events),
    SourceForm =.. [Kind, Name, Start],
    Program = mnn_program(
                  Name, meta(SourceForm, Events), Predicates,
                  proof([]), trace([])).

ordered_unique([], _, []).
ordered_unique([Name|Names], Seen, Unique) :-
    (   memberchk(Name, Seen)
    ->  ordered_unique(Names, Seen, Unique)
    ;   Unique = [Name|Rest],
        ordered_unique(Names, [Name|Seen], Rest)
    ).

grammar_predicates([], _, _, _, []).
grammar_predicates([Name|Names], Rules, Kind, ProgramName,
                   [Predicate|Predicates]) :-
    grammar_clauses(Rules, Name, Kind, ProgramName, 1, Clauses),
    Predicate = mnn_pred(Name/2, ['?', '?'], [any, any], Clauses, original),
    grammar_predicates(Names, Rules, Kind, ProgramName, Predicates).

grammar_clauses([], _, _, _, _, []).
grammar_clauses([rule(Name, Symbols)|Rules], Target, Kind, ProgramName,
                RuleId, Clauses) :-
    (   Name == Target
    ->  grammar_clause(Name, Symbols, Kind, ProgramName, RuleId, Clause),
        Clauses = [Clause|Rest]
    ;   Clauses = Rest
    ),
    NextId is RuleId + 1,
    grammar_clauses(Rules, Target, Kind, ProgramName, NextId, Rest).

grammar_clause(Name, Symbols, Kind, ProgramName, RuleId,
               mnn_clause(RuleId, Head, Body, Source)) :-
    Input = _,
    Rest = _,
    Head =.. [Name, Input, Rest],
    symbols_body(Symbols, Input, Rest, Goals),
    conjunction(Goals, Body),
    SourceKind =.. [Kind, ProgramName],
    Source = source(SourceKind, RuleId).

symbols_body([], Rest, Rest, []).
symbols_body([terminal(Token)|Symbols], Input, Rest,
             [Input = [Token|Next]|Goals]) :-
    symbols_body(Symbols, Next, Rest, Goals).
symbols_body([nonterminal(Name)|Symbols], Input, Rest,
             [Call|Goals]) :-
    Next = _,
    Call =.. [Name, Input, Next],
    symbols_body(Symbols, Next, Rest, Goals).

conjunction([], true).
conjunction([Goal], Goal) :-
    !.
conjunction([Goal|Goals], conj(Goal, Rest)) :-
    conjunction(Goals, Rest).

clause_event(Id, clause(Id)).

grammar_proof(Rule, Proof) :-
    Proof = proof([proof_step(
                       1, Rule, [],
                       equivalent(domain(all), modes(all)))]),
    memberchk(Rule, [incorporate_cfg, incorporate_dcg]).

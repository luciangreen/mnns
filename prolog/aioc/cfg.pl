:- module(mnn_aioc_cfg,
          [ incorporate_cfg/4
          ]).

:- use_module(library(error)).
:- use_module('../proof/proof_checker').

incorporate_cfg(Name, Grammar, Program, Proof) :-
    must_be(atom, Name),
    Source = cfg_source(Name, Grammar),
    (   valid_cfg_source(Name, Grammar)
    ->  build_cfg_program(Name, Grammar, Program),
        cfg_incorporation_proof(Proof),
        mnn_proof_checker:check_proof(Program, Source, Proof, accepted)
    ;   throw(error(domain_error(cfg_source, Source), _))
    ).

valid_cfg_source(Name, cfg(Start, Rules)) :-
    atom(Name),
    atom(Start),
    is_list(Rules),
    Rules = [_|_],
    acyclic_term(Rules),
    cfg_nonterminals(Rules, Nonterminals),
    memberchk(Start, Nonterminals),
    maplist(valid_cfg_rule(Nonterminals), Rules).

cfg_nonterminals(Rules, Nonterminals) :-
    maplist(cfg_rule_nonterminal, Rules, AllNonterminals),
    list_to_set(AllNonterminals, Nonterminals).

cfg_rule_nonterminal(rule(Nonterminal, _), Nonterminal) :-
    atom(Nonterminal).

valid_cfg_rule(Nonterminals, rule(Nonterminal, Symbols)) :-
    atom(Nonterminal),
    memberchk(Nonterminal, Nonterminals),
    is_list(Symbols),
    maplist(valid_cfg_symbol(Nonterminals), Symbols).

valid_cfg_symbol(_, terminal(Token)) :-
    ground(Token),
    acyclic_term(Token).
valid_cfg_symbol(Nonterminals, nonterminal(Nonterminal)) :-
    atom(Nonterminal),
    memberchk(Nonterminal, Nonterminals).

build_cfg_program(Name, cfg(Start, Rules), Program) :-
    cfg_nonterminals(Rules, Nonterminals),
    cfg_predicate_mapping(Name, Nonterminals, Mapping),
    cfg_mapped_predicate(Start, Mapping, StartPredicate),
    WrapperHead =.. [Name, Tokens],
    StartGoal =.. [StartPredicate, Tokens, []],
    Wrapper = mnn_pred(
                  Name/1, ['?'], [any],
                  [mnn_clause(1, WrapperHead, StartGoal,
                              source(cfg(Name), 1))],
                  original),
    cfg_rule_predicates(
        Nonterminals, Rules, Mapping, Name, 2, RulePredicates),
    append([Wrapper], RulePredicates, Predicates),
    cfg_clause_events(Predicates, Events),
    Program = mnn_program(
                  Name, meta(cfg(Name), Events), Predicates,
                  proof([]), trace([])).

cfg_predicate_mapping(Name, Nonterminals, Mapping) :-
    cfg_predicate_mapping(Name, Nonterminals, 1, Mapping).

cfg_predicate_mapping(_, [], _, []).
cfg_predicate_mapping(Name, [Nonterminal|Nonterminals], Index,
                      [Nonterminal-Predicate|Mapping]) :-
    format(atom(Predicate), '~w__cfg_nt_~d', [Name, Index]),
    NextIndex is Index + 1,
    cfg_predicate_mapping(Name, Nonterminals, NextIndex, Mapping).

cfg_mapped_predicate(Nonterminal, [Nonterminal-Predicate|_], Predicate) :-
    !.
cfg_mapped_predicate(Nonterminal, [_|Mapping], Predicate) :-
    cfg_mapped_predicate(Nonterminal, Mapping, Predicate).

cfg_rule_predicates([], _, _, _, _, []).
cfg_rule_predicates([Nonterminal|Nonterminals], Rules, Mapping,
                    Name, ClauseId,
                    Predicates) :-
    rules_for_nonterminal(Nonterminal, Rules, Selected),
    cfg_mapped_predicate(Nonterminal, Mapping, PredicateName),
    cfg_rule_clauses(Selected, PredicateName, Mapping, Name, ClauseId,
                     Clauses, NextClauseId),
    Predicate = mnn_pred(
                    PredicateName/2, ['?', '?'], [any, any],
                    Clauses, original),
    cfg_rule_predicates(Nonterminals, Rules, Mapping, Name,
                        NextClauseId, Rest),
    Predicates = [Predicate|Rest].

rules_for_nonterminal(Nonterminal, Rules, Selected) :-
    include(rule_for_nonterminal(Nonterminal), Rules, Selected).

rule_for_nonterminal(Nonterminal, rule(Other, _)) :-
    Nonterminal == Other.

cfg_rule_clauses([], _, _, _, ClauseId, [], ClauseId).
cfg_rule_clauses([rule(_, Symbols)|Rules], PredicateName, Mapping, Name, ClauseId,
                 [Clause|Clauses], NextClauseId) :-
    Input = _,
    Output = _,
    Head =.. [PredicateName, Input, Output],
    cfg_rule_body(Symbols, Input, Output, Mapping, Body),
    Clause = mnn_clause(
                 ClauseId, Head, Body, source(cfg(Name), ClauseId)),
    FollowingClauseId is ClauseId + 1,
    cfg_rule_clauses(Rules, PredicateName, Mapping, Name, FollowingClauseId,
                     Clauses, NextClauseId).

cfg_rule_body([], Input, Output, _, Input = Output).
cfg_rule_body([Symbol|Symbols], Input, Output, Mapping, Body) :-
    cfg_symbol_goal(Symbol, Input, NextInput, Mapping, Goal),
    (   Symbols == []
    ->  cfg_last_goal(Goal, NextInput, Output, Body)
    ;   cfg_rule_body(Symbols, NextInput, Output, Mapping, Rest),
        Body = (Goal, Rest)
    ).

cfg_last_goal(Goal, Input, Output, (Goal, Input = Output)).

cfg_symbol_goal(terminal(Token), Input, Rest, _, Input = [Token|Rest]).
cfg_symbol_goal(nonterminal(Nonterminal), Input, Rest, Mapping, Goal) :-
    cfg_mapped_predicate(Nonterminal, Mapping, Predicate),
    Goal =.. [Predicate, Input, Rest].

cfg_clause_events(Predicates, Events) :-
    cfg_clause_ids(Predicates, [], ClauseIds),
    reverse(ClauseIds, Events).

cfg_clause_ids([], Events, Events).
cfg_clause_ids([mnn_pred(_, _, _, Clauses, _)|Predicates], Acc, Events) :-
    cfg_clause_ids_in_predicate(Clauses, Acc, Next),
    cfg_clause_ids(Predicates, Next, Events).

cfg_clause_ids_in_predicate([], Events, Events).
cfg_clause_ids_in_predicate([mnn_clause(Id, _, _, _)|Clauses],
                            Acc, Events) :-
    cfg_clause_ids_in_predicate(Clauses, [clause(Id)|Acc], Events).

cfg_incorporation_proof(
    proof([proof_step(1, incorporate_cfg, [],
                      equivalent(domain(all), modes(all)))])).

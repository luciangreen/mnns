:- module(mnn_proof_checker,
          [ check_proof/4
          ]).

check_proof(Program, Original, Proof, Result) :-
    (   mnn_program_term(Program),
        mnn_program_term(Original)
    ->  check_supported_proof(Program, Original, Proof, Result)
    ;   Result = rejected(invalid_program)
    ).

mnn_program_term(Program) :-
    nonvar(Program),
    functor(Program, mnn_program, 5).

check_supported_proof(Program, Original, Proof, Result) :-
    (   valid_identity_proof(Proof)
    ->  (   Program =@= Original
        ->  Result = accepted
        ;   Result = rejected(programs_differ)
        )
    ;   valid_goal_reordering_proof(Program, Original, Proof)
    ->  Result = accepted
    ;   valid_definition_introduction_proof(Program, Original, Proof)
    ->  Result = accepted
    ;   valid_definition_rewrite_proof(Program, Original, Proof)
    ->  Result = accepted
    ;   valid_findall_to_fold_proof(Program, Original, Proof)
    ->  Result = accepted
    ;   valid_proof_sequence(Program, Original, Proof)
    ->  Result = accepted
    ;   Result = rejected(invalid_or_unsupported_proof)
    ).

valid_identity_proof(Proof) :-
    ground(Proof),
    Proof = proof([Step]),
    Step = proof_step(Id, Rule, Premises, Conclusion),
    integer(Id),
    Id > 0,
    Rule == identity,
    Premises == [],
    Conclusion = equivalent(domain(Domain), modes(Modes)),
    ground(Domain),
    ground(Modes).

valid_goal_reordering_proof(Program, Original, Proof) :-
    ground(Proof),
    Proof = proof([proof_step(Id, reorder_goals, [],
                              equivalent(domain(Domain), modes(Modes)))]),
    integer(Id),
    Id > 0,
    ground(Domain),
    ground(Modes),
    valid_reordering_program(Original),
    copy_term(Original, OriginalCopy),
    reorder_program(OriginalCopy, Reordered, Count),
    Count =:= 1,
    Program =@= Reordered.

valid_definition_introduction_proof(Program, Original, Proof) :-
    ground(Proof),
    Proof = proof([proof_step(Id, introduce_definition, [],
                              equivalent(domain(Domain), modes(Modes)))]),
    integer(Id),
    Id > 0,
    ground(Domain),
    ground(Modes),
    valid_rewrite_program(Original),
    copy_term(Original, OriginalCopy),
    introduce_definition(OriginalCopy, Introduced),
    Program =@= Introduced.

valid_reordering_program(mnn_program(_, _, Predicates, _, _)) :-
    is_list(Predicates),
    maplist(valid_reordering_predicate, Predicates).

valid_reordering_predicate(Predicate) :-
    nonvar(Predicate),
    functor(Predicate, mnn_pred, 5),
    arg(4, Predicate, Clauses),
    is_list(Clauses),
    maplist(valid_reordering_clause, Clauses).

valid_reordering_clause(Clause) :-
    nonvar(Clause),
    functor(Clause, mnn_clause, 4).

reorder_program(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, ReorderedPredicates, Proof, Trace),
    Count) :-
    reorder_predicates(Predicates, ReorderedPredicates, Count).

reorder_predicates([], [], 0).
reorder_predicates([Predicate|Predicates], [Reordered|Rest], Count) :-
    reorder_predicate(Predicate, Reordered, PredicateCount),
    reorder_predicates(Predicates, Rest, RestCount),
    Count is PredicateCount + RestCount.

reorder_predicate(
    mnn_pred(Key, Modes, Domains, Clauses, Status),
    mnn_pred(Key, Modes, Domains, ReorderedClauses, Status),
    Count) :-
    reorder_clauses(Clauses, ReorderedClauses, Count).

reorder_clauses([], [], 0).
reorder_clauses(
    [mnn_clause(Id, Head, Body, Source)|Clauses],
    [mnn_clause(Id, Head, ReorderedBody, Source)|Rest],
    Count) :-
    reorder_goal(Body, ReorderedBody, ClauseCount),
    reorder_clauses(Clauses, Rest, RestCount),
    Count is ClauseCount + RestCount.

reorder_goal(conj(Left, Right), conj(Right, Left), 1) :-
    safe_ground_test(Left),
    safe_ground_test(Right),
    !.
reorder_goal(conj(Left, Right), conj(ReorderedLeft, Right), Count) :-
    reorder_goal(Left, ReorderedLeft, Count).
reorder_goal(conj(Left, Right), conj(Left, ReorderedRight), Count) :-
    reorder_goal(Right, ReorderedRight, Count).
reorder_goal(Goal, Goal, 0).

safe_ground_test(Goal) :-
    ground(Goal),
    Goal =.. [Name, Argument],
    ground(Argument),
    memberchk(Name, [atom, atomic, compound, ground, integer, is_list, number]).
safe_ground_test(Goal) :-
    ground(Goal),
    supported_arithmetic_filter(Goal),
    checked_filter_result(Goal, _).
safe_ground_test(is(Expected, Expression)) :-
    ground(Expected),
    arithmetic_expression(Expression),
    ground(Expression),
    checked_arithmetic_value(Expression, _).

valid_definition_rewrite_proof(Program, Original, Proof) :-
    ground(Proof),
    Proof = proof([proof_step(Id, Rule, [],
                              equivalent(domain(Domain), modes(Modes)))]),
    memberchk(Rule, [unfold, fold]),
    integer(Id),
    Id > 0,
    ground(Domain),
    ground(Modes),
    valid_rewrite_program(Original),
    copy_term(Original, OriginalCopy),
    rewrite_program(Rule, OriginalCopy, Rewritten),
    Program =@= Rewritten.

valid_findall_to_fold_proof(Program, Original, Proof) :-
    ground(Proof),
    Proof = proof([proof_step(Id, findall_to_fold, [],
                              equivalent(domain(Domain), modes(Modes)))]),
    integer(Id),
    Id > 0,
    ground(Domain),
    ground(Modes),
    valid_rewrite_program(Original),
    copy_term(Original, OriginalCopy),
    findall_to_fold_program(OriginalCopy, Rewritten),
    Program =@= Rewritten.

valid_proof_sequence(Program, Original, proof(Steps)) :-
    ground(Steps),
    is_list(Steps),
    Steps = [_,_|_],
    apply_proof_steps(Steps, Original, Rewritten),
    Program =@= Rewritten.

apply_proof_steps([], Program, Program).
apply_proof_steps([Step|Steps], Program0, Program) :-
    apply_proof_step(Step, Program0, Program1),
    apply_proof_steps(Steps, Program1, Program).

apply_proof_step(
    proof_step(Id, Rule, Premises,
               equivalent(domain(Domain), modes(Modes))),
    Program, Rewritten) :-
    integer(Id),
    Id > 0,
    Premises == [],
    ground(Domain),
    ground(Modes),
    apply_proof_rule(Rule, Program, Rewritten).

apply_proof_rule(identity, Program, Program).
apply_proof_rule(reorder_goals, Program, Rewritten) :-
    valid_reordering_program(Program),
    copy_term(Program, ProgramCopy),
    reorder_program(ProgramCopy, Rewritten, Count),
    Count =:= 1.
apply_proof_rule(introduce_definition, Program, Rewritten) :-
    valid_rewrite_program(Program),
    copy_term(Program, ProgramCopy),
    introduce_definition(ProgramCopy, Rewritten).
apply_proof_rule(Rule, Program, Rewritten) :-
    memberchk(Rule, [unfold, fold]),
    valid_rewrite_program(Program),
    copy_term(Program, ProgramCopy),
    rewrite_program(Rule, ProgramCopy, Rewritten).
apply_proof_rule(findall_to_fold, Program, Rewritten) :-
    valid_rewrite_program(Program),
    copy_term(Program, ProgramCopy),
    findall_to_fold_program(ProgramCopy, Rewritten).

findall_to_fold_program(
    mnn_program(Name, meta(Source, Events), Predicates, Proof, Trace),
    mnn_program(Name, meta(Source, UpdatedEvents), UpdatedPredicates,
                Proof, Trace)) :-
    is_list(Events),
    is_list(Predicates),
    findall_candidate(Predicates, PredicateIndex, ClauseIndex,
                      Values, Results),
    fresh_loop_name(Predicates, Loop),
    max_clause_id(Predicates, MaxClauseId),
    FirstGeneratedId is MaxClauseId + 1,
    SecondGeneratedId is FirstGeneratedId + 1,
    replace_findall_candidate(Predicates, PredicateIndex, ClauseIndex,
                              Loop, Values, Results, UpdatedPredicates0),
    make_copy_loop(Loop, FirstGeneratedId, SecondGeneratedId, Helper),
    append(UpdatedPredicates0, [Helper], UpdatedPredicates),
    append(Events, [clause(FirstGeneratedId), clause(SecondGeneratedId)],
           UpdatedEvents).

findall_candidate(Predicates, PredicateIndex, ClauseIndex, Values, Results) :-
    nth1(PredicateIndex, Predicates, Predicate),
    arg(4, Predicate, Clauses),
    nth1(ClauseIndex, Clauses, Clause),
    arg(3, Clause, Body),
    nonvar(Body),
    Body = findall(Template, Generator, Results),
    findall_candidate_values(Predicates, Template, Generator, Values).

findall_candidate_values(_, Template, member(Value, List), Values) :-
    ground(List),
    is_list(List),
    member_candidate_values(List, Value, Template, [], Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, nth0(Index, List, Value), Filters),
    ground(List),
    is_list(List),
    supported_nth_index(Index),
    maplist(supported_arithmetic_filter, Filters),
    nth_candidate_values(List, 0, Index, Value, Template, Filters, Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, nth1(Index, List, Value), Filters),
    ground(List),
    is_list(List),
    supported_nth_index(Index),
    maplist(supported_arithmetic_filter, Filters),
    nth_candidate_values(List, 1, Index, Value, Template, Filters, Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, between(Low, High, Value), Filters),
    Filters \= [],
    integer(Low),
    integer(High),
    (   var(Value)
    ;   integer(Value)
    ),
    maplist(supported_arithmetic_filter, Filters),
    between_candidate_numbers(Low, High, Numbers),
    between_candidate_values(Numbers, Value, Template, Filters, Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, length(List, Length), Filters),
    Filters \= [],
    ground(List),
    is_list(List),
    (   var(Length)
    ;   integer(Length),
        Length >= 0
    ),
    maplist(supported_arithmetic_filter, Filters),
    length(List, ActualLength),
    copy_term((Length, Template, Filters),
              (LengthCopy, TemplateCopy, FiltersCopy)),
    (   LengthCopy = ActualLength
    ->  checked_filters_result(FiltersCopy, FilterResult),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy]
        ;   Values = []
        )
    ;   Values = []
    ).
findall_candidate_values(_, Template, length(List, Length), Values) :-
    ground(List),
    is_list(List),
    (   var(Length)
    ;   integer(Length),
        Length >= 0
    ),
    length(List, ActualLength),
    copy_term((Length, Template), (LengthCopy, TemplateCopy)),
    (   LengthCopy = ActualLength
    ->  ground(TemplateCopy),
        Values = [TemplateCopy]
    ;   Values = []
    ).
findall_candidate_values(_, Template, between(Low, High, Value), Values) :-
    integer(Low),
    integer(High),
    (   var(Value)
    ;   integer(Value)
    ),
    between_candidate_numbers(Low, High, Numbers),
    between_candidate_values(Numbers, Value, Template, Values).
findall_candidate_values(_, Template, select(Value, List, Rest), Values) :-
    ground(List),
    is_list(List),
    select_candidate_values(List, Value, Rest, Template, Values).
findall_candidate_values(_, Template, append(Prefix, Suffix, List), Values) :-
    ground(List),
    is_list(List),
    append_candidate_values(List, Prefix, Suffix, Template, Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, select(Value, List, Rest), Filters),
    Filters \= [],
    ground(List),
    is_list(List),
    maplist(supported_arithmetic_filter, Filters),
    select_candidate_values(List, Value, Rest, Template, Filters, Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, append(Prefix, Suffix, List), Filters),
    Filters \= [],
    ground(List),
    is_list(List),
    maplist(supported_arithmetic_filter, Filters),
    append_candidate_values(List, Prefix, Suffix, Template, Filters, Values).
findall_candidate_values(_, Template, Generator, Values) :-
    generator_parts(Generator, member(Value, List), Filters),
    Filters \= [],
    ground(List),
    is_list(List),
    maplist(supported_arithmetic_filter, Filters),
    member_candidate_values(List, Value, Template, Filters, Values).
findall_candidate_values(Predicates, Template, Generator, Values) :-
    generator_parts(Generator, Goal, Filters),
    Filters \= [],
    maplist(supported_arithmetic_filter, Filters),
    fact_generator_clauses(Predicates, Goal, Clauses),
    fact_candidate_values(Clauses, Goal, Template, Filters, Values).
findall_candidate_values(Predicates, Template, Generator, Values) :-
    fact_generator_clauses(Predicates, Generator, Clauses),
    fact_candidate_values(Clauses, Generator, Template, Values).
findall_candidate_values(Predicates, Template, Generator, Values) :-
    generator_parts(Generator, Goal, Filters),
    rule_generator_clauses(Predicates, Goal),
    maplist(supported_arithmetic_filter, Filters),
    rule_generator_values(Predicates, Goal, Template, Filters, Values).

rule_generator_clauses(Predicates, Goal) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    Key = Name/Arity,
    rule_predicate_supported(Predicates, Key, [], Clauses),
    once(( member(mnn_clause(_, Head, Body, _), Clauses),
           (   Body \== true
           ;   \+ ground(Head)
           )
         )).

rule_predicate_supported(Predicates, Key, Visited, Clauses) :-
    \+ memberchk(Key, Visited),
    findall(FoundClauses,
            ( member(mnn_pred(FoundKey, _, _, FoundClauses, _), Predicates),
              FoundKey == Key
            ),
            [Clauses]),
    Clauses \= [],
    maplist(rule_clause_supported(Predicates, [Key|Visited]), Clauses).

rule_clause_supported(_, _, mnn_clause(_, Head, true, _)) :-
    ground(Head),
    !.
rule_clause_supported(Predicates, Visited, mnn_clause(_, Head, Body, _)) :-
    nonvar(Head),
    callable(Head),
    rule_goal_supported(Predicates, Body, Visited).

rule_goal_supported(_, true, _) :-
    !.
rule_goal_supported(_, fail, _) :-
    !.
rule_goal_supported(Predicates, conj(Left, Right), Visited) :-
    !,
    rule_goal_supported(Predicates, Left, Visited),
    rule_goal_supported(Predicates, Right, Visited).
rule_goal_supported(Predicates, disj(Left, Right), Visited) :-
    !,
    rule_goal_supported(Predicates, Left, Visited),
    rule_goal_supported(Predicates, Right, Visited).
rule_goal_supported(Predicates, Goal, _) :-
    nonvar(Goal),
    Goal = findall(_, _, _),
    !,
    nested_findall_supported(Predicates, Goal).
rule_goal_supported(Predicates, Goal, _) :-
    safe_rule_unification(Goal),
    !,
    \+ member(mnn_pred((=)/2, _, _, _, _), Predicates).
rule_goal_supported(_, Goal, _) :-
    supported_arithmetic_filter(Goal),
    !.
rule_goal_supported(Predicates, Goal, Visited) :-
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    rule_predicate_supported(Predicates, Name/Arity, Visited, _).

rule_generator_values(Predicates, Goal, Template, Filters, Values) :-
    copy_term((Goal, Template, Filters),
              (GoalCopy, TemplateCopy, FiltersCopy)),
    catch(( findall(candidate(TemplateCopy, FiltersCopy),
                    rule_goal(Predicates, GoalCopy, []),
                    Candidates),
            rule_candidate_values(Candidates, Values)
          ),
          _,
          fail).

rule_goal(_, true, _) :-
    !.
rule_goal(_, fail, _) :-
    !,
    fail.
rule_goal(Predicates, Goal, _) :-
    safe_rule_unification(Goal),
    !,
    (   member(mnn_pred((=)/2, _, _, _, _), Predicates)
    ->  throw(invalid_rule_generator)
    ;   Goal = (Left = Right),
        Left = Right,
        (   acyclic_term((Left, Right))
        ->  true
        ;   throw(invalid_rule_generator)
        )
    ).
rule_goal(Predicates, conj(Left, Right), Visited) :-
    !,
    rule_goal(Predicates, Left, Visited),
    rule_goal(Predicates, Right, Visited).
rule_goal(Predicates, disj(Left, Right), Visited) :-
    !,
    (   rule_goal(Predicates, Left, Visited)
    ;   rule_goal(Predicates, Right, Visited)
    ).
rule_goal(_, Filter, _) :-
    supported_arithmetic_filter(Filter),
    !,
    checked_rule_filter(Filter, true).
rule_goal(Predicates, Goal, _) :-
    nonvar(Goal),
    Goal = findall(_, _, _),
    !,
    nested_findall_values(Predicates, Goal).
rule_goal(Predicates, Goal, Visited) :-
    functor(Goal, Name, Arity),
    Key = Name/Arity,
    \+ memberchk(Key, Visited),
    member(mnn_pred(FoundKey, _, _, Clauses, _), Predicates),
    FoundKey == Key,
    member(mnn_clause(_, Head, Body, _), Clauses),
    copy_term((Head, Body), (HeadCopy, BodyCopy)),
    Goal = HeadCopy,
    rule_goal(Predicates, BodyCopy, [Key|Visited]).

safe_rule_unification(Goal) :-
    nonvar(Goal),
    Goal = (Left = Right),
    acyclic_term((Left, Right)).

nested_findall_supported(Predicates, Goal) :-
    copy_term(Goal, GoalCopy),
    nested_findall_values(Predicates, GoalCopy).

nested_findall_values(
    Predicates, findall(Template, Generator, Results)) :-
    nested_builtin_generator(Predicates, Generator),
    copy_term((Template, Generator),
              (TemplateCopy, GeneratorCopy)),
    findall_candidate_values(Predicates, TemplateCopy, GeneratorCopy, Values),
    Results = Values.

nested_builtin_generator(Predicates, Generator) :-
    generator_parts(Generator, Goal, Filters),
    nonvar(Goal),
    callable(Goal),
    functor(Goal, Name, Arity),
    memberchk(Name/Arity,
              [member/2, select/3, append/3, length/2,
               nth0/3, nth1/3, between/3]),
    Key = Name/Arity,
    \+ member(mnn_pred(Key, _, _, _, _), Predicates),
    nested_builtin_domain(Goal),
    maplist(supported_arithmetic_filter, Filters).

nested_builtin_domain(member(_, List)) :-
    ground(List),
    is_list(List).
nested_builtin_domain(select(_, List, _)) :-
    ground(List),
    is_list(List).
nested_builtin_domain(append(_, _, List)) :-
    ground(List),
    is_list(List).
nested_builtin_domain(length(List, _)) :-
    ground(List),
    is_list(List).
nested_builtin_domain(nth0(_, List, _)) :-
    ground(List),
    is_list(List).
nested_builtin_domain(nth1(_, List, _)) :-
    ground(List),
    is_list(List).
nested_builtin_domain(between(Low, High, Value)) :-
    integer(Low),
    integer(High),
    (   var(Value)
    ;   integer(Value)
    ).

rule_candidate_values([], []).
rule_candidate_values([candidate(Template, Filters)|Candidates], Values) :-
    checked_rule_filters(Filters, FilterResult),
    (   FilterResult == true
    ->  ground(Template),
        Values = [Template|Rest]
    ;   Values = Rest
    ),
    rule_candidate_values(Candidates, Rest).

checked_rule_filters([], true).
checked_rule_filters([Filter|Filters], Result) :-
    checked_rule_filter(Filter, FilterResult),
    (   FilterResult == true
    ->  checked_rule_filters(Filters, Result)
    ;   Result = false
    ).

checked_rule_filter(Filter, Result) :-
    (   checked_filter_result(Filter, FilterResult)
    ->  true
    ;   throw(invalid_rule_filter)
    ),
    Result = FilterResult.

generator_parts(conj(Goal, Filters), Generator, Conditions) :-
    !,
    flatten_generator_conjunction(conj(Goal, Filters), Goals),
    Goals = [Generator|Conditions].
generator_parts(Generator, Generator, []).

flatten_generator_conjunction(conj(Left, Right), Goals) :-
    !,
    flatten_generator_conjunction(Left, LeftGoals),
    flatten_generator_conjunction(Right, RightGoals),
    append(LeftGoals, RightGoals, Goals).
flatten_generator_conjunction(Goal, [Goal]).

supported_arithmetic_filter(Filter) :-
    nonvar(Filter),
    functor(Filter, Name, 2),
    memberchk(Name, [>, >=, <, =<, =:=, =\=]),
    arg(1, Filter, Left),
    arg(2, Filter, Right),
    arithmetic_expression(Left),
    arithmetic_expression(Right).

arithmetic_expression(Expression) :-
    number(Expression),
    !.
arithmetic_expression(Expression) :-
    var(Expression),
    !.
arithmetic_expression(Expression) :-
    compound(Expression),
    compound_name_arguments(Expression, Name, Arguments),
    arithmetic_operator(Name, Arity),
    length(Arguments, Arity),
    maplist(arithmetic_expression, Arguments).

arithmetic_operator(+, 1).
arithmetic_operator(-, 1).
arithmetic_operator(abs, 1).
arithmetic_operator(+, 2).
arithmetic_operator(-, 2).
arithmetic_operator(*, 2).
arithmetic_operator(/, 2).
arithmetic_operator(//, 2).
arithmetic_operator(mod, 2).
arithmetic_operator(rem, 2).

fact_generator_clauses(Predicates, Generator, Clauses) :-
    nonvar(Generator),
    callable(Generator),
    \+ predicate_property(system:Generator, built_in),
    functor(Generator, Name, Arity),
    Key = Name/Arity,
    findall(FoundClauses,
            ( member(mnn_pred(FoundKey, _, _, FoundClauses, _), Predicates),
              FoundKey == Key
            ),
            [Clauses]),
    Clauses \= [],
    maplist(ground_fact_clause, Clauses).

ground_fact_clause(mnn_clause(_, Head, true, _)) :-
    ground(Head).

fact_candidate_values([], _, _, []).
fact_candidate_values([mnn_clause(_, Head, true, _)|Clauses],
                      Generator, Template, Values) :-
    copy_term((Generator, Template), (GeneratorCopy, TemplateCopy)),
    (   GeneratorCopy = Head
    ->  ground(TemplateCopy),
        Values = [TemplateCopy|Rest]
    ;   Values = Rest
    ),
    fact_candidate_values(Clauses, Generator, Template, Rest).

fact_candidate_values([], _, _, _, []).
fact_candidate_values([mnn_clause(_, Head, true, _)|Clauses],
                      Generator, Template, Filters, Values) :-
    copy_term((Generator, Template, Filters),
              (GeneratorCopy, TemplateCopy, FiltersCopy)),
    (   GeneratorCopy = Head
    ->  checked_filters_result(FiltersCopy, FilterResult),
        fact_candidate_values(Clauses, Generator, Template, Filters, Rest),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   fact_candidate_values(Clauses, Generator, Template, Filters, Values)
    ).

checked_filters_result([], true).
checked_filters_result([Filter|Filters], Result) :-
    checked_filter_result(Filter, FilterResult),
    (   FilterResult == true
    ->  checked_filters_result(Filters, Result)
    ;   Result = false
    ).

checked_filter_result(Filter, Result) :-
    Filter =.. [Name, Left, Right],
    ground((Left, Right)),
    checked_arithmetic_value(Left, LeftValue),
    checked_arithmetic_value(Right, RightValue),
    checked_comparison(Name, LeftValue, RightValue, Result).

checked_arithmetic_value(Expression, Value) :-
    arithmetic_expression(Expression),
    ground(Expression),
    catch(Value is Expression, _, fail).

checked_comparison(>, Left, Right, Result) :-
    (Left > Right -> Result = true ; Result = false).
checked_comparison(>=, Left, Right, Result) :-
    (Left >= Right -> Result = true ; Result = false).
checked_comparison(<, Left, Right, Result) :-
    (Left < Right -> Result = true ; Result = false).
checked_comparison(=<, Left, Right, Result) :-
    (Left =< Right -> Result = true ; Result = false).
checked_comparison(=:=, Left, Right, Result) :-
    (Left =:= Right -> Result = true ; Result = false).
checked_comparison(=\=, Left, Right, Result) :-
    (Left =\= Right -> Result = true ; Result = false).

between_candidate_numbers(Low, High, Numbers) :-
    (   Low > High
    ->  Numbers = []
    ;   Count is High - Low + 1,
        Count =< 10000,
        findall(Number, between(Low, High, Number), Numbers)
    ).

between_candidate_values(Numbers, Value, Template, Values) :-
    between_candidate_values(Numbers, Value, Template, [], Values).

between_candidate_values([], _, _, _, []).
between_candidate_values([Number|Numbers], Value, Template, Filters, Values) :-
    copy_term((Value, Template, Filters),
              (ValueCopy, TemplateCopy, FiltersCopy)),
    (   ValueCopy = Number
    ->  checked_filters_result(FiltersCopy, FilterResult),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   Values = Rest
    ),
    between_candidate_values(Numbers, Value, Template, Filters, Rest).

select_candidate_values(List, Value, Rest, Template, Values) :-
    findall(candidate(TemplateCopy, Match),
            ( selection(List, Selected, Remaining),
              copy_term((Value, Rest, Template),
                        (ValueCopy, RestCopy, TemplateCopy)),
              (   ValueCopy = Selected,
                  RestCopy = Remaining
              ->  (   ground(TemplateCopy)
                  ->  Match = selected
                  ;   Match = unground
                  )
              ;   Match = excluded
              )
            ),
            Candidates),
    collect_select_values(Candidates, Values).

select_candidate_values(List, Value, Rest, Template, Filters, Values) :-
    select_candidate_values(List, [], Value, Rest, Template, Filters, Values).

select_candidate_values([], _, _, _, _, _, []).
select_candidate_values([Candidate|Candidates], Prefix, Value, Rest, Template,
                        Filters, Values) :-
    copy_term((Value, Rest, Template, Filters),
              (ValueCopy, RestCopy, TemplateCopy, FiltersCopy)),
    reverse(Prefix, PrefixInOrder),
    append(PrefixInOrder, Candidates, SelectedRest),
    (   ValueCopy = Candidate,
        RestCopy = SelectedRest
    ->  checked_filters_result(FiltersCopy, FilterResult),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|RemainingValues]
        ;   Values = RemainingValues
        )
    ;   Values = RemainingValues
    ),
    select_candidate_values(Candidates, [Candidate|Prefix], Value, Rest,
                           Template, Filters, RemainingValues).

append_candidate_values(List, Prefix, Suffix, Template, Values) :-
    append_candidate_values(List, Prefix, Suffix, Template, [], Values).

append_candidate_values(List, Prefix, Suffix, Template, Filters, Values) :-
    findall(split(PrefixPart, SuffixPart),
            append(PrefixPart, SuffixPart, List),
            Splits),
    maplist(checked_append_split(Prefix, Suffix, Template, Filters),
            Splits, Candidates),
    checked_append_candidate_values(Candidates, Values).

checked_append_candidate_values([], []).
checked_append_candidate_values([skip|Candidates], Values) :-
    checked_append_candidate_values(Candidates, Values).
checked_append_candidate_values([result(Template)|Candidates],
                               [Template|Values]) :-
    checked_append_candidate_values(Candidates, Values).

checked_append_split(Prefix, Suffix, Template, Filters,
                     split(PrefixPart, SuffixPart), Candidate) :-
    copy_term((Prefix, Suffix, Template, Filters),
              (PrefixCopy, SuffixCopy, TemplateCopy, FiltersCopy)),
    (   PrefixCopy = PrefixPart,
        SuffixCopy = SuffixPart
    ->  checked_filters_result(FiltersCopy, FilterResult),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Candidate = result(TemplateCopy)
        ;   Candidate = skip
        )
    ;   Candidate = skip
    ).

member_candidate_values([], _, _, _, []).
member_candidate_values([Candidate|Candidates], Value, Template, Filters,
                        Values) :-
    copy_term((Value, Template, Filters),
              (ValueCopy, TemplateCopy, FiltersCopy)),
    (   ValueCopy = Candidate
    ->  checked_filters_result(FiltersCopy, FilterResult),
        member_candidate_values(Candidates, Value, Template, Filters, Rest),
        (   FilterResult == true
        ->  ground(TemplateCopy),
            Values = [TemplateCopy|Rest]
        ;   Values = Rest
        )
    ;   member_candidate_values(Candidates, Value, Template, Filters, Values)
    ).

nth_candidate_values([], _, _, _, _, _, []).
nth_candidate_values([Candidate|Candidates], IndexValue, Index, Value,
                     Template, Filters, Values) :-
    copy_term((Index, Value, Template, Filters),
              (IndexCopy, ValueCopy, TemplateCopy, FiltersCopy)),
    (   IndexCopy = IndexValue,
        ValueCopy = Candidate
    ->  checked_filters_result(FiltersCopy, FilterResult)
    ;   FilterResult = false
    ),
    NextIndex is IndexValue + 1,
    nth_candidate_values(Candidates, NextIndex, Index, Value, Template,
                         Filters, Rest),
    (   FilterResult == true
    ->  ground(TemplateCopy),
        Values = [TemplateCopy|Rest]
    ;   Values = Rest
    ).

collect_select_values([], []).
collect_select_values([candidate(_, unground)|_], _) :-
    !,
    fail.
collect_select_values([candidate(_, excluded)|Candidates], Values) :-
    !,
    collect_select_values(Candidates, Values).
collect_select_values([candidate(Template, selected)|Candidates],
                      [Template|Values]) :-
    collect_select_values(Candidates, Values).

selection([Value|Values], Value, Values).
selection([Head|Values], Value, [Head|Rest]) :-
    selection(Values, Value, Rest).

supported_nth_index(Index) :-
    var(Index),
    !.
supported_nth_index(Index) :-
    integer(Index).

replace_findall_candidate(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    1, ClauseIndex, Loop, Values, Results,
    [mnn_pred(Key, Modes, Domains, UpdatedClauses, Status)|Predicates]) :-
    !,
    replace_findall_clause(Clauses, ClauseIndex, Loop, Values, Results,
                           UpdatedClauses).
replace_findall_candidate(
    [Predicate|Predicates], PredicateIndex, ClauseIndex, Loop, Values,
    Results, [Predicate|UpdatedPredicates]) :-
    PredicateIndex > 1,
    NextPredicateIndex is PredicateIndex - 1,
    replace_findall_candidate(Predicates, NextPredicateIndex, ClauseIndex,
                              Loop, Values, Results, UpdatedPredicates).

replace_findall_clause(
    [mnn_clause(Id, Head, findall(_, _, _), Location)|Clauses],
    1, Loop, Values, Results,
    [mnn_clause(Id, Head, LoopCall, Location)|Clauses]) :-
    !,
    LoopCall =.. [Loop, Values, Results].
replace_findall_clause(
    [Clause|Clauses], ClauseIndex, Loop, Values, Results,
    [Clause|UpdatedClauses]) :-
    ClauseIndex > 1,
    NextClauseIndex is ClauseIndex - 1,
    replace_findall_clause(Clauses, NextClauseIndex, Loop, Values, Results,
                           UpdatedClauses).

fresh_loop_name(Predicates, Name) :-
    fresh_loop_name(1, Predicates, Name).

fresh_loop_name(Index, Predicates, Name) :-
    format(atom(Candidate), 'mnn_loop2_~d', [Index]),
    (   member(mnn_pred(Key, _, _, _, _), Predicates),
        Key == Candidate/2
    ->  NextIndex is Index + 1,
        fresh_loop_name(NextIndex, Predicates, Name)
    ;   Name = Candidate
    ).

max_clause_id(Predicates, MaxClauseId) :-
    findall(Id,
            ( member(mnn_pred(_, _, _, Clauses, _), Predicates),
              member(mnn_clause(Id, _, _, _), Clauses)
            ),
            Ids),
    maplist(integer, Ids),
    (   Ids = []
    ->  MaxClauseId = 0
    ;   max_list(Ids, MaxClauseId)
    ).

make_copy_loop(Name, FirstId, SecondId,
               mnn_pred(Name/2, ['?', '?'], [any, any],
                        [mnn_clause(FirstId, EmptyHead, true,
                                    generated(loop2)),
                         mnn_clause(SecondId, RecursiveHead,
                                    RecursiveBody, generated(loop2))],
                        generated(loop2))) :-
    EmptyHead =.. [Name, [], []],
    RecursiveHead =.. [Name, [Value|Values], [Value|Results]],
    RecursiveBody =.. [Name, Values, Results].

valid_rewrite_program(mnn_program(_, _, Predicates, _, _)) :-
    is_list(Predicates),
    maplist(valid_rewrite_predicate, Predicates).

valid_rewrite_predicate(Predicate) :-
    nonvar(Predicate),
    functor(Predicate, mnn_pred, 5),
    arg(4, Predicate, Clauses),
    is_list(Clauses),
    maplist(valid_rewrite_clause, Clauses).

valid_rewrite_clause(Clause) :-
    nonvar(Clause),
    functor(Clause, mnn_clause, 4).

rewrite_program(Rule,
                mnn_program(Name, Meta, Predicates, Proof, Trace),
                mnn_program(Name, Meta, RewrittenPredicates, Proof, Trace)) :-
    rewrite_predicates(Rule, Predicates, Predicates,
                       RewrittenPredicates).

rewrite_predicates(Rule, Definitions, [Predicate|Predicates],
                   [Rewritten|Predicates]) :-
    rewrite_predicate(Rule, Definitions, Predicate, Rewritten).
rewrite_predicates(Rule, Definitions, [Predicate|Predicates],
                   [Predicate|RewrittenPredicates]) :-
    rewrite_predicates(Rule, Definitions, Predicates,
                       RewrittenPredicates).

rewrite_predicate(
    Rule, Definitions,
    mnn_pred(Key, Modes, Domains, Clauses, Status),
    mnn_pred(Key, Modes, Domains, RewrittenClauses, Status)) :-
    rewrite_clauses(Rule, Definitions, Key, Clauses, RewrittenClauses).

rewrite_clauses(Rule, Definitions, Key,
                [Clause|Clauses], [Rewritten|Clauses]) :-
    rewrite_clause(Rule, Definitions, Key, Clause, Rewritten).
rewrite_clauses(Rule, Definitions, Key,
                [Clause|Clauses], [Clause|RewrittenClauses]) :-
    rewrite_clauses(Rule, Definitions, Key, Clauses,
                    RewrittenClauses).

rewrite_clause(
    Rule, Definitions, Key,
    mnn_clause(Id, Head, Body, Source),
    mnn_clause(Id, Head, RewrittenBody, Source)) :-
    rewrite_goal(Rule, Definitions, Key, Body, RewrittenBody).

rewrite_goal(Rule, Definitions, Key, Goal, RewrittenGoal) :-
    nonvar(Goal),
    rewrite_nonvar_goal(Rule, Definitions, Key, Goal, RewrittenGoal).

rewrite_nonvar_goal(unfold, Definitions, _, Goal, RewrittenBody) :-
    safe_definition(Definitions, _, Head, Body),
    unfold_definition(Goal, Head, Body, RewrittenBody).
rewrite_nonvar_goal(fold, Definitions, CallerKey, Goal, RewrittenHead) :-
    safe_definition(Definitions, DefinitionKey, Head, Body),
    CallerKey \== DefinitionKey,
    fold_definition(Goal, Head, Body, RewrittenHead).
rewrite_nonvar_goal(Rule, Definitions, Key, conj(Left, Right),
                    conj(RewrittenLeft, Right)) :-
    rewrite_goal(Rule, Definitions, Key, Left, RewrittenLeft).
rewrite_nonvar_goal(Rule, Definitions, Key, conj(Left, Right),
                    conj(Left, RewrittenRight)) :-
    rewrite_goal(Rule, Definitions, Key, Right, RewrittenRight).
rewrite_nonvar_goal(Rule, Definitions, Key, disj(Left, Right),
                    disj(RewrittenLeft, Right)) :-
    rewrite_goal(Rule, Definitions, Key, Left, RewrittenLeft).
rewrite_nonvar_goal(Rule, Definitions, Key, disj(Left, Right),
                    disj(Left, RewrittenRight)) :-
    rewrite_goal(Rule, Definitions, Key, Right, RewrittenRight).
rewrite_nonvar_goal(Rule, Definitions, Key, ite(If, Then, Else),
                    ite(RewrittenIf, Then, Else)) :-
    rewrite_goal(Rule, Definitions, Key, If, RewrittenIf).
rewrite_nonvar_goal(Rule, Definitions, Key, ite(If, Then, Else),
                    ite(If, RewrittenThen, Else)) :-
    rewrite_goal(Rule, Definitions, Key, Then, RewrittenThen).
rewrite_nonvar_goal(Rule, Definitions, Key, ite(If, Then, Else),
                    ite(If, Then, RewrittenElse)) :-
    rewrite_goal(Rule, Definitions, Key, Else, RewrittenElse).
rewrite_nonvar_goal(Rule, Definitions, Key, not(Goal),
                    not(RewrittenGoal)) :-
    rewrite_goal(Rule, Definitions, Key, Goal, RewrittenGoal).

introduce_definition(
    mnn_program(Name, Meta, Predicates, Proof, Trace),
    mnn_program(Name, Meta, IntroducedPredicates, Proof, Trace)) :-
    clause_ids(Predicates, Ids),
    maplist(integer, Ids),
    helper_name(Predicates, 1, HelperName),
    (   Ids == []
    ->  HelperId = 1
    ;   max_list(Ids, MaxId),
        HelperId is MaxId + 1
    ),
    introduce_in_predicates(Predicates, HelperName, Introduced, Call, Goal),
    introduced_definition(HelperName, Goal, HelperKey, HelperModes,
                         HelperDomains, HelperHead, HelperBody),
    append(Introduced,
           [mnn_pred(HelperKey, HelperModes, HelperDomains,
                     [mnn_clause(HelperId, HelperHead, HelperBody,
                                 source(generated, 0))],
                     introduced)],
           IntroducedPredicates).

clause_ids([], []).
clause_ids([mnn_pred(_, _, _, Clauses, _)|Predicates], Ids) :-
    clause_ids_in_predicates(Predicates, Clauses, Ids).

clause_ids_in_predicates(Predicates, Clauses, Ids) :-
    clause_ids_in_clauses(Clauses, ClauseIds),
    clause_ids(Predicates, PredicateIds),
    append(ClauseIds, PredicateIds, Ids).

clause_ids_in_clauses([], []).
clause_ids_in_clauses([mnn_clause(Id, _, _, _)|Clauses], [Id|Ids]) :-
    clause_ids_in_clauses(Clauses, Ids).

helper_name(Predicates, Index, Name) :-
    format(atom(Name), 'mnn_definition_~d', [Index]),
    (   helper_name_exists(Predicates, Name)
    ->  Next is Index + 1,
        helper_name(Predicates, Next, Name)
    ;   true
    ).

helper_name_exists(Predicates, Name) :-
    (   predicate_key_exists(Predicates, Name/0)
    ;   predicate_key_exists(Predicates, Name/1)
    ).

predicate_key_exists([Predicate|_], Key) :-
    arg(1, Predicate, ExistingKey),
    ExistingKey == Key,
    !.
predicate_key_exists([_|Predicates], Key) :-
    predicate_key_exists(Predicates, Key).

introduce_in_predicates([Predicate|Predicates], Name,
                        [Introduced|Predicates], Call, Goal) :-
    introduce_in_predicate(Predicate, Name, Introduced, Call, Goal),
    !.
introduce_in_predicates([Predicate|Predicates], Name,
                        [Predicate|Introduced], Call, Goal) :-
    introduce_in_predicates(Predicates, Name, Introduced, Call, Goal).

introduce_in_predicate(
    mnn_pred(Key, Modes, Domains, Clauses, Status), Name,
    mnn_pred(Key, Modes, Domains, IntroducedClauses, Status), Call, Goal) :-
    introduce_in_clauses(Clauses, Name, IntroducedClauses, Call, Goal).

introduce_in_clauses([Clause|Clauses], Name,
                     [Introduced|Clauses], Call, Goal) :-
    introduce_in_clause(Clause, Name, Introduced, Call, Goal),
    !.
introduce_in_clauses([Clause|Clauses], Name,
                     [Clause|Introduced], Call, Goal) :-
    introduce_in_clauses(Clauses, Name, Introduced, Call, Goal).

introduce_in_clause(
    mnn_clause(Id, Head, Body, Source), Name,
    mnn_clause(Id, Head, IntroducedBody, Source), Call, Goal) :-
    introduce_in_goal(Body, Name, IntroducedBody, Call, Goal).

introduce_in_goal(Goal, Name, Name, Goal, Goal) :-
    ground(Goal),
    safe_pure_goal(Goal),
    !.
introduce_in_goal(Goal, Name, Call, Goal, Goal) :-
    term_variables(Goal, [Argument]),
    safe_variable_pure_goal(Goal, Argument),
    Call =.. [Name, Argument],
    !.
introduce_in_goal(conj(Left, Right), Name,
                  conj(Introduced, Right), Call, Goal) :-
    introduce_in_goal(Left, Name, Introduced, Call, Goal),
    !.
introduce_in_goal(conj(Left, Right), Name,
                  conj(Left, Introduced), Call, Goal) :-
    introduce_in_goal(Right, Name, Introduced, Call, Goal).
introduce_in_goal(disj(Left, Right), Name,
                  disj(Introduced, Right), Call, Goal) :-
    introduce_in_goal(Left, Name, Introduced, Call, Goal),
    !.
introduce_in_goal(disj(Left, Right), Name,
                  disj(Left, Introduced), Call, Goal) :-
    introduce_in_goal(Right, Name, Introduced, Call, Goal).
introduce_in_goal(ite(If, Then, Else), Name,
                  ite(Introduced, Then, Else), Call, Goal) :-
    introduce_in_goal(If, Name, Introduced, Call, Goal),
    !.
introduce_in_goal(ite(If, Then, Else), Name,
                  ite(If, Introduced, Else), Call, Goal) :-
    introduce_in_goal(Then, Name, Introduced, Call, Goal),
    !.
introduce_in_goal(ite(If, Then, Else), Name,
                  ite(If, Then, Introduced), Call, Goal) :-
    introduce_in_goal(Else, Name, Introduced, Call, Goal).
introduce_in_goal(not(Goal), Name, not(Introduced), Call, Extracted) :-
    introduce_in_goal(Goal, Name, Introduced, Call, Extracted).

introduced_definition(Name, Goal, Name/0, [], [], Name, Goal) :-
    term_variables(Goal, []),
    !.
introduced_definition(Name, Goal, Name/1, ['?'], [any], Head, Body) :-
    term_variables(Goal, [Argument]),
    copy_term(Argument-Goal, FreshArgument-Body),
    Head =.. [Name, FreshArgument].

safe_definition(Predicates, Key, Head, Body) :-
    member(mnn_pred(Key, _, _, [mnn_clause(_, Head, Body, _)], _),
           Predicates),
    functor(Head, Name, Arity),
    Key == Name/Arity,
    (   ground(Head),
        ground(Body),
        safe_pure_goal(Body)
    ;   safe_variable_definition(Head, Body)
    ),
    findall(Clauses,
            ( member(mnn_pred(OtherKey, _, _, Clauses, _), Predicates),
              OtherKey == Key
            ),
            [[mnn_clause(_, _, _, _)]]).

unfold_definition(Goal, Head, Body, Body) :-
    ground(Head),
    Goal == Head.
unfold_definition(Goal, Head, Body, RewrittenBody) :-
    safe_variable_definition(Head, Body),
    copy_term(Head-Body, FreshHead-FreshBody),
    Goal = FreshHead,
    RewrittenBody = FreshBody.

fold_definition(Goal, Head, Body, Head) :-
    ground(Body),
    Goal == Body.
fold_definition(Goal, Head, Body, RewrittenHead) :-
    safe_variable_definition(Head, Body),
    copy_term(Head-Body, FreshHead-FreshBody),
    Goal =@= FreshBody,
    Goal = FreshBody,
    RewrittenHead = FreshHead.

safe_variable_definition(Head, Body) :-
    Head =.. [_Name, Argument],
    var(Argument),
    nonvar(Body),
    safe_variable_pure_goal(Body, Argument).

safe_variable_pure_goal(true, _).
safe_variable_pure_goal(fail, _).
safe_variable_pure_goal(Goal, Argument) :-
    nonvar(Goal),
    Goal =.. [Name, GoalArgument],
    GoalArgument == Argument,
    memberchk(Name, [atom, atomic, compound, ground, integer, is_list, number]).
safe_variable_pure_goal(conj(Left, Right), Argument) :-
    safe_variable_pure_goal(Left, Argument),
    safe_variable_pure_goal(Right, Argument).
safe_variable_pure_goal(disj(Left, Right), Argument) :-
    safe_variable_pure_goal(Left, Argument),
    safe_variable_pure_goal(Right, Argument).

safe_pure_goal(true).
safe_pure_goal(fail).
safe_pure_goal(Goal) :-
    safe_ground_test(Goal).
safe_pure_goal(conj(Left, Right)) :-
    safe_pure_goal(Left),
    safe_pure_goal(Right).
safe_pure_goal(disj(Left, Right)) :-
    safe_pure_goal(Left),
    safe_pure_goal(Right).

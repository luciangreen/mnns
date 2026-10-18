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
    findall(PredicateIndex-ClauseIndex,
            findall_candidate(Predicates, PredicateIndex, ClauseIndex, _, _),
            [PredicateIndex-ClauseIndex]),
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
    findall_candidate_values(Template, Generator, Values).

findall_candidate_values(Template, member(Value, List), List) :-
    Template == Value,
    ground(List),
    is_list(List).
findall_candidate_values(Template, nth0(Index, List, Value), Indices) :-
    Template == Index,
    var(Index),
    var(Value),
    Index \== Value,
    ground(List),
    is_list(List),
    list_indices(List, Indices).
findall_candidate_values(Template, nth1(Index, List, Value), Indices) :-
    Template == Index,
    var(Index),
    var(Value),
    Index \== Value,
    ground(List),
    is_list(List),
    list_indices(List, 1, Indices).
findall_candidate_values(Template, length(List, Length), Values) :-
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
findall_candidate_values(Template, select(Value, List, Rest), Values) :-
    ground(List),
    is_list(List),
    select_candidate_values(List, Value, Rest, Template, Values).

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

list_indices(List, Indices) :-
    list_indices(List, 0, Indices).

list_indices([], _, []).
list_indices([_|Values], Index, [Index|Indices]) :-
    NextIndex is Index + 1,
    list_indices(Values, NextIndex, Indices).

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

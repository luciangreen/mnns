:- module(mnn_plop,
          [ optimize_program/3,
            optimize_predicate/4
          ]).

:- use_module('../loop2/loop2').
:- use_module('../proof/proof_checker').

optimize_program(Program, Optimized, Report) :-
    run_pipeline(Program, whole_program, Optimized, Report).

optimize_predicate(Program, Key, Optimized, Report) :-
    (   valid_predicate_key(Key)
    ->  (   program_has_predicate(Program, Key)
        ->  run_pipeline(Program, predicate(Key), Optimized, Report)
        ;   unchanged(Program, [kept(unknown_predicate(Key))], Optimized,
                      Report)
        )
    ;   unchanged(Program, [kept(invalid_predicate_key(Key))], Optimized,
                  Report)
    ).

run_pipeline(Program, Scope, Optimized, plop_report(Events, Proof, Status)) :-
    mnn_loop2:convert_program(Program, Candidate,
                              loop2_report(Conversions)),
    run_candidate(Conversions, Program, Candidate, Scope,
                  Optimized, Events, Proof, Status).

run_candidate([], Program, _, _, Program,
              [kept(no_supported_conversion)], Proof, unchanged) :-
    !,
    identity_proof(Proof).
run_candidate([Conversion], Program, Candidate, Scope, Optimized,
              [applied(findall_to_fold, Conversions)], Proof, accepted) :-
    Conversions = [Conversion],
    scope_accepts(Scope, Program, Candidate),
    findall_proof(Proof),
    mnn_proof_checker:check_proof(Candidate, Program, Proof, accepted),
    !,
    Optimized = Candidate.
run_candidate(Conversions, Program, _, _, Program,
              [kept(multiple_conversions(Count))], Proof, unchanged) :-
    length(Conversions, Count),
    Count > 1,
    !,
    identity_proof(Proof).
run_candidate([_], Program, Candidate, predicate(Key), Program,
              [kept(requested_predicate_not_converted(Key))], Proof,
              unchanged) :-
    !,
    identity_proof(Proof),
    target_is_unchanged(Program, Candidate, Key).
run_candidate([_], Program, _, _, Program,
              [kept(proof_rejected)], Proof, unchanged) :-
    !,
    identity_proof(Proof).

scope_accepts(whole_program, _, _).
scope_accepts(predicate(Key), Program, Candidate) :-
    target_is_only_modified(Program, Candidate, Key).

target_is_only_modified(
    mnn_program(_, _, OriginalPredicates, _, _),
    mnn_program(_, _, CandidatePredicates, _, _),
    Key) :-
    member(mnn_pred(Key, _, _, _, _), OriginalPredicates),
    maplist(unchanged_unselected_predicate(CandidatePredicates, Key),
            OriginalPredicates).

target_is_unchanged(
    mnn_program(_, _, OriginalPredicates, _, _),
    mnn_program(_, _, CandidatePredicates, _, _),
    Key) :-
    member(OriginalPredicate, OriginalPredicates),
    OriginalPredicate = mnn_pred(FoundKey, _, _, _, _),
    FoundKey == Key,
    member(CandidatePredicate, CandidatePredicates),
    CandidatePredicate = mnn_pred(CandidateKey, _, _, _, _),
    CandidateKey == Key,
    OriginalPredicate =@= CandidatePredicate.

unchanged_unselected_predicate(_, Key,
                               mnn_pred(FoundKey, _, _, _, _)) :-
    FoundKey == Key,
    !.
unchanged_unselected_predicate(CandidatePredicates, _,
                               OriginalPredicate) :-
    OriginalPredicate = mnn_pred(FoundKey, _, _, _, _),
    member(CandidatePredicate, CandidatePredicates),
    CandidatePredicate = mnn_pred(CandidateKey, _, _, _, _),
    CandidateKey == FoundKey,
    OriginalPredicate =@= CandidatePredicate.

program_has_predicate(mnn_program(_, _, Predicates, _, _), Key) :-
    member(mnn_pred(FoundKey, _, _, _, _), Predicates),
    FoundKey == Key.

valid_predicate_key(Name/Arity) :-
    atom(Name),
    integer(Arity),
    Arity >= 0.

findall_proof(
    proof([proof_step(
               1, findall_to_fold, [],
               equivalent(domain(supported_finite_generator_subset),
                          modes(preserved)))])).

identity_proof(
    proof([proof_step(
               1, identity, [],
               equivalent(domain(all), modes(all)))])).

unchanged(Program, Events, Program, plop_report(Events, Proof, unchanged)) :-
    identity_proof(Proof).

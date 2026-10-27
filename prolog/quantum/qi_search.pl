:- module(mnn_qi_search,
          [ qi_search/4,
            qi_export/3
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module('../aioc/size').
:- use_module('../plop/plop').
:- use_module('../proof/proof_checker').

qi_search(Program, Options, Best,
          qi_report(Seed, Links, CandidateSummaries, History,
                    selected(BestName), BestSize, proof_steps(ProofSize),
                    rewrites_tried(RewriteCount))) :-
    validate_program(Program),
    must_be(list, Options),
    search_options(Options, Seed, Links),
    validate_links(Program, Links),
    identity_proof(IdentityProof),
    mnn_proof_checker:check_proof(Program, Program, IdentityProof, accepted),
    program_cost(Program, OriginalCost),
    seeded_amplitude(Seed, original, OriginalAmplitude),
    Original = qi_candidate(original, Program, IdentityProof,
                            OriginalAmplitude, OriginalCost),
    program_predicate_keys(Program, PredicateKeys),
    proposal_specs(PredicateKeys, Proposals),
    maplist(evaluate_proposal(Program, Seed, Links, OriginalCost),
            Proposals, Results),
    partition(candidate_result, Results, CandidateResults, AttemptResults),
    maplist(candidate_result_value, CandidateResults, GeneratedCandidates),
    unique_candidates([Original|GeneratedCandidates], Candidates),
    maplist(result_history, AttemptResults, AttemptHistory),
    maplist(result_history, CandidateResults, CandidateHistory),
    append([original(OriginalAmplitude, OriginalCost)],
           CandidateHistory, SearchHistory),
    append(SearchHistory, AttemptHistory, History),
    maplist(candidate_summary, Candidates, CandidateSummaries),
    maplist(candidate_sort_key, Candidates, KeyedCandidates),
    keysort(KeyedCandidates, [_-Selected|_]),
    Selected = qi_candidate(BestName, Best, Proof, _, _),
    mnn_proof_checker:check_proof(Best, Program, Proof, accepted),
    program_cost(Best, BestSize),
    proof_step_count(Proof, ProofSize),
    length(Proposals, RewriteCount),
    !.

qi_export(Program, qasm, File) :-
    validate_program(Program),
    must_be(atom, File),
    program_predicate_keys(Program, PredicateKeys),
    length(PredicateKeys, PredicateCount),
    QubitCount is max(1, PredicateCount),
    setup_call_cleanup(
        open(File, write, Stream, [encoding(utf8)]),
        write_qasm(Stream, QubitCount),
        close(Stream)).

search_options(Options, Seed, Links) :-
    findall(Value, member(seed(Value), Options), Seeds),
    findall(Value, member(links(Value), Options), LinkSets),
    reject_unknown_options(Options),
    single_option_value(Seeds, 0, Seed),
    single_option_value(LinkSets, [], Links),
    must_be(integer, Seed),
    (   Seed >= 0
    ->  true
    ;   throw(error(domain_error(not_less_than_zero, Seed), _))
    ),
    must_be(list, Links).

single_option_value([], Default, Default).
single_option_value([Value], _, Value) :-
    !.
single_option_value([_,_|_], _, _) :-
    throw(error(domain_error(unique_option, seed_or_links), _)).

reject_unknown_options([]).
reject_unknown_options([seed(_)|Options]) :-
    !,
    reject_unknown_options(Options).
reject_unknown_options([links(_)|Options]) :-
    !,
    reject_unknown_options(Options).
reject_unknown_options([Option|_]) :-
    throw(error(domain_error(qi_search_option, Option), _)).

validate_links(_, []).
validate_links(Program, [Link|Links]) :-
    (   Link = qi_link(Left, Right),
        valid_predicate_key(Left),
        valid_predicate_key(Right),
        program_has_predicate(Program, Left),
        program_has_predicate(Program, Right)
    ->  validate_links(Program, Links)
    ;   throw(error(domain_error(qi_link, Link), _))
    ).

program_predicate_keys(mnn_program(_, _, Predicates, _, _), Keys) :-
    maplist(predicate_key, Predicates, Keys).

predicate_key(mnn_pred(Key, _, _, _, _), Key).

proposal_specs(Keys, [whole_program|Proposals]) :-
    maplist(predicate_proposal, Keys, Proposals).

predicate_proposal(Key, predicate(Key)).

evaluate_proposal(Program, Seed, Links, OriginalCost, Spec, Result) :-
    run_proposal(Spec, Program, Candidate, Proof, _Status),
    (   mnn_proof_checker:check_proof(Candidate, Program, Proof, ProofResult)
    ->  true
    ;   ProofResult = rejected(checker_failed)
    ),
    proposal_name(Spec, Name),
    program_cost(Candidate, Cost),
    proof_step_count(Proof, ProofSize),
    linked_rechecks(Spec, Links, Candidate, Program, Proof, Rechecks),
    proposal_result(ProofResult, Candidate, Proof, Name, Seed, OriginalCost,
                    Cost, ProofSize, Rechecks, Result).

run_proposal(whole_program, Program, Candidate, Proof, Status) :-
    mnn_plop:optimize_program(
        Program, Candidate, plop_report(_, Proof, Status)).
run_proposal(predicate(Key), Program, Candidate, Proof, Status) :-
    mnn_plop:optimize_predicate(
        Program, Key, Candidate, plop_report(_, Proof, Status)).

proposal_result(accepted, Candidate, Proof, Name, Seed, OriginalCost, Cost,
                ProofSize, Rechecks,
                candidate_result(
                    qi_candidate(Name, Candidate, Proof, Amplitude, Cost),
                    event(Name, proposal(Candidate), accepted, Update,
                          amplitude(Amplitude),
                          cost(Cost), proof_steps(ProofSize), Rechecks,
                          Evidence))) :-
    !,
    seeded_amplitude(Seed, Name, InitialAmplitude),
    (   Cost < OriginalCost
    ->  Amplitude is InitialAmplitude + 10,
        Update = amplified,
        Evidence = evidence(supporting(proof_accepted,
                                       size_reduction(OriginalCost, Cost)),
                           opposing(none))
    ;   Amplitude is max(0, InitialAmplitude - 10),
        Update = attenuated,
        Evidence = evidence(supporting(proof_accepted),
                           opposing(no_size_reduction(OriginalCost, Cost)))
    ).
proposal_result(ProofResult, Candidate, _, Name, Seed, OriginalCost, _, ProofSize,
                Rechecks,
                attempt_result(
                    event(Name, proposal(Candidate), rejected(ProofResult),
                          attenuated,
                          amplitude(Amplitude), cost(OriginalCost),
                          proof_steps(ProofSize), Rechecks,
                          evidence(supporting(none),
                                   opposing(proof_rejected(ProofResult)))))) :-
    seeded_amplitude(Seed, Name, InitialAmplitude),
    Amplitude is max(0, InitialAmplitude - 10).

linked_rechecks(whole_program, _, _, _, _, none).
linked_rechecks(predicate(Key), Links, Candidate, Original, Proof,
                linked_rechecks(Events)) :-
    predicate_changed(Key, Candidate, Original),
    !,
    findall(Other,
            ( member(qi_link(Left, Right), Links),
              ( Key == Left, Other = Right
              ; Key == Right, Other = Left
              )
            ),
            Others0),
    sort(Others0, Others),
    maplist(recheck_linked(Candidate, Original, Proof), Others, Events).
linked_rechecks(predicate(_), _, _, _, _, none).

recheck_linked(Candidate, Original, Proof, Key,
               linked_recheck(Key, Result)) :-
    mnn_proof_checker:check_proof(Candidate, Original, Proof, Result).

proposal_name(whole_program, whole_program).
proposal_name(predicate(Name/Arity), Atom) :-
    format(atom(Atom), 'predicate_~w_~d', [Name, Arity]).

seeded_amplitude(Seed, Name, Amplitude) :-
    atom_codes(Name, Codes),
    sum_list(Codes, NameSum),
    Amplitude is 100 + ((Seed + NameSum) mod 5).

program_cost(Program, Cost) :-
    mnn_aioc_size:measure_program_size(
        Program, program_size(_, _, _, _, weighted_total(Cost))).

proof_step_count(proof(Steps), Count) :-
    !,
    length(Steps, Count).
proof_step_count(_, 0).

candidate_result(candidate_result(_, _)).

candidate_result_value(candidate_result(Candidate, _), Candidate).

result_history(candidate_result(_, Event), Event).
result_history(attempt_result(Event), Event).

candidate_summary(qi_candidate(Name, Program, Proof, Amplitude, Cost),
                  candidate(Name, Program, Proof, amplitude(Amplitude),
                            cost(Cost))).

candidate_sort_key(qi_candidate(Name, Program, Proof, Amplitude, Cost),
                   key(NegativeAmplitude, Cost, Name)-
                       qi_candidate(Name, Program, Proof, Amplitude, Cost)) :-
    NegativeAmplitude is -Amplitude.

unique_candidates(Candidates, Unique) :-
    unique_candidates(Candidates, [], Unique).

unique_candidates([], _, []).
unique_candidates([Candidate|Candidates], Seen, Unique) :-
    Candidate = qi_candidate(_, Program, _, _, _),
    (   member(qi_candidate(_, Existing, _, _, _), Seen),
        Program =@= Existing
    ->  unique_candidates(Candidates, Seen, Unique)
    ;   Unique = [Candidate|Rest],
        unique_candidates(Candidates, [Candidate|Seen], Rest)
    ).

program_has_predicate(mnn_program(_, _, Predicates, _, _), Key) :-
    member(mnn_pred(FoundKey, _, _, _, _), Predicates),
    FoundKey == Key.

predicate_changed(Key, Candidate, Original) :-
    program_predicate(Candidate, Key, CandidatePredicate),
    program_predicate(Original, Key, OriginalPredicate),
    CandidatePredicate \=@= OriginalPredicate.

program_predicate(mnn_program(_, _, Predicates, _, _), Key, Predicate) :-
    member(Predicate, Predicates),
    Predicate = mnn_pred(FoundKey, _, _, _, _),
    FoundKey == Key.

validate_program(Program) :-
    (   Program = mnn_program(_, _, Predicates, _, _),
        is_list(Predicates),
        maplist(valid_predicate_record, Predicates)
    ->  true
    ;   throw(error(domain_error(mnn_program, Program), _))
    ).

valid_predicate_record(mnn_pred(Key, _, _, _, _)) :-
    valid_predicate_key(Key).

valid_predicate_key(Name/Arity) :-
    atom(Name),
    integer(Arity),
    Arity >= 0.

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))])).

write_qasm(Stream, QubitCount) :-
    format(Stream, 'OPENQASM 3.0;~n', []),
    format(Stream, 'include "stdgates.inc";~n', []),
    format(Stream, '// Schematic predicate-selection register; no execution.~n',
           []),
    format(Stream, 'qubit[~d] q;~n', [QubitCount]),
    format(Stream, 'bit[~d] c;~n', [QubitCount]),
    write_qasm_qubits(Stream, 0, QubitCount).

write_qasm_qubits(_, Index, Count) :-
    Index >= Count,
    !.
write_qasm_qubits(Stream, Index, Count) :-
    format(Stream, 'h q[~d];~n', [Index]),
    format(Stream, 'measure q[~d] -> c[~d];~n', [Index, Index]),
    Next is Index + 1,
    write_qasm_qubits(Stream, Next, Count).

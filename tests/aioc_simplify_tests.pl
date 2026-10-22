:- begin_tests(mnn_aioc_simplify).

:- use_module('../prolog/aioc/simplify').
:- use_module('../prolog/proof/proof_checker').

test(removes_redundant_true_conjuncts_with_sequential_checked_steps) :-
    sample_program(Original),
    mnn_aioc_simplify:simplify_program(
        Original, Simplified, Proof,
        simplification_report(
            changes(2), OriginalSize, SimplifiedSize,
            structural_effect(smaller))),
    Simplified = mnn_program(
                     sample, meta(source, [clause(1)]),
                     [mnn_pred(p/1, ['?'], [any],
                               [mnn_clause(1, p(X), q(X), source(test, 1))],
                               original)],
                     proof([]), trace([])),
    mnn_proof_checker:check_proof(Simplified, Original, Proof, accepted),
    OriginalSize = program_size(_, _, _, _,
                                weighted_total(OriginalTotal)),
    SimplifiedSize = program_size(_, _, _, _,
                                  weighted_total(SimplifiedTotal)),
    assertion(SimplifiedTotal < OriginalTotal).

test(retains_unchanged_program_with_identity_proof) :-
    unchanged_program(Program),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, Proof,
        simplification_report(
            changes(0), Size, Size, structural_effect(unchanged))),
    assertion(Simplified =@= Program),
    assertion(Proof = proof([proof_step(
                                 1, identity, [],
                                 equivalent(domain(all), modes(all)))])).

test(does_not_remove_true_when_source_defines_true_predicate) :-
    defined_true_program(Original),
    mnn_aioc_simplify:simplify_program(
        Original, Simplified, Proof,
        simplification_report(changes(0), _, _, structural_effect(unchanged))),
    assertion(Simplified =@= Original),
    mnn_proof_checker:check_proof(Simplified, Original, Proof, accepted).

test(simplifies_conjunctions_nested_under_control_goals) :-
    Program = mnn_program(
                  sample, meta(source, [clause(1)]),
                  [mnn_pred(p/1, ['?'], [any],
                            [mnn_clause(
                                 1, p(X), disj(once(conj(true, q(X))), fail),
                                 source(test, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, Proof,
        simplification_report(changes(2), _, _, structural_effect(smaller))),
    Simplified = mnn_program(
                     sample, meta(source, [clause(1)]),
                     [mnn_pred(p/1, ['?'], [any],
                               [mnn_clause(
                                    1, p(Y), once(q(Y)),
                                    source(test, 1))],
                               original)],
                     proof([]), trace([])),
    mnn_proof_checker:check_proof(Simplified, Program, Proof, accepted).

test(removes_fail_disjuncts_with_sequential_checked_steps) :-
    Program = mnn_program(
                  sample, meta(source, [clause(1)]),
                  [mnn_pred(p/1, ['?'], [any],
                            [mnn_clause(
                                 1, p(X),
                                 disj(fail, conj(q(X), disj(r(X), fail))),
                                 source(test, 1))],
                            original)],
                  proof([]), trace([])),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, Proof,
        simplification_report(changes(2), _, _, structural_effect(smaller))),
    Simplified = mnn_program(
                     sample, meta(source, [clause(1)]),
                     [mnn_pred(p/1, ['?'], [any],
                               [mnn_clause(
                                    1, p(Y), conj(q(Y), r(Y)), source(test, 1))],
                               original)],
                     proof([]), trace([])),
    mnn_proof_checker:check_proof(Simplified, Program, Proof, accepted).

test(does_not_remove_fail_when_source_defines_fail_predicate) :-
    Program = mnn_program(
                  sample, meta(source, [clause(1), clause(2)]),
                  [mnn_pred(p/0, [], [any],
                            [mnn_clause(1, p, disj(fail, q), source(test, 1))],
                            original),
                   mnn_pred(fail/0, [], [any],
                            [mnn_clause(2, fail, true, source(test, 2))],
                            original)],
                  proof([]), trace([])),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, Proof,
        simplification_report(changes(0), _, _, structural_effect(unchanged))),
    assertion(Simplified =@= Program),
    mnn_proof_checker:check_proof(Simplified, Program, Proof, accepted).

test(does_not_instantiate_an_unbound_clause_body) :-
    variable_body_program(Program, Body),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, _,
        simplification_report(changes(0), _, _, structural_effect(unchanged))),
    assertion(var(Body)),
    assertion(Simplified =@= Program).

test(does_not_treat_an_unbound_conjunct_as_true) :-
    variable_conjunct_program(Program, Goal),
    mnn_aioc_simplify:simplify_program(
        Program, Simplified, _,
        simplification_report(changes(0), _, _, structural_effect(unchanged))),
    assertion(var(Goal)),
    assertion(Simplified =@= Program).

test(rejects_unjustified_true_removal) :-
    sample_program(Original),
    BadCandidate = mnn_program(
                       sample, meta(source, [clause(1)]),
                       [mnn_pred(p/1, ['?'], [any],
                                 [mnn_clause(1, p(_), disj(q(_), true),
                                             source(test, 1))],
                                 original)],
                       proof([]), trace([])),
    Proof = proof([proof_step(
                       1, remove_true_conjunct, [],
                       equivalent(domain(any), modes(all)))]),
    mnn_proof_checker:check_proof(
        BadCandidate, Original, Proof,
        rejected(invalid_or_unsupported_proof)).

sample_program(
    mnn_program(
        sample, meta(source, [clause(1)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(
                       1, p(X), conj(true, conj(q(X), true)),
                       source(test, 1))],
                  original)],
        proof([]), trace([]))).

unchanged_program(
    mnn_program(
        sample, meta(source, [clause(1)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(1, p(X), true, source(test, 1))],
                  original)],
        proof([]), trace([]))).

defined_true_program(
    mnn_program(
        sample, meta(source, [clause(1), clause(2)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(1, p(X), conj(true, q(X)), source(test, 1))],
                  original),
         mnn_pred(true/0, [], [], [mnn_clause(2, true, fail, source(test, 2))],
                  original)],
        proof([]), trace([]))).

variable_body_program(
    mnn_program(
        sample, meta(source, [clause(1)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(1, p(X), Body, source(test, 1))],
                  original)],
        proof([]), trace([])),
    Body).

variable_conjunct_program(
    mnn_program(
        sample, meta(source, [clause(1)]),
        [mnn_pred(p/1, ['?'], [any],
                  [mnn_clause(1, p(X), conj(Goal, q(X)), source(test, 1))],
                  original)],
        proof([]), trace([])),
    Goal).

:- end_tests(mnn_aioc_simplify).

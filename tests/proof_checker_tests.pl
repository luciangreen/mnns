:- begin_tests(mnn_proof_checker).

:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/proof/proof_renderer').

test(accept_identity_proof_for_alpha_equivalent_programs) :-
    Program = mnn_program(sample, meta(file, []),
                          [mnn_pred(value/1, ['?'], [any],
                                    [mnn_clause(1, value(X), true,
                                                source(file, 1))],
                                    original)],
                          proof([]), trace([])),
    Original = mnn_program(sample, meta(file, []),
                           [mnn_pred(value/1, ['?'], [any],
                                     [mnn_clause(1, value(Y), true,
                                                 source(file, 1))],
                                     original)],
                           proof([]), trace([])),
    identity_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_identity_proof_for_different_programs) :-
    Program = mnn_program(sample, meta(file, []), [], proof([]), trace([])),
    Original = mnn_program(other, meta(file, []), [], proof([]), trace([])),
    identity_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(programs_differ)).

test(accept_reordering_of_ground_pure_tests) :-
    program_with_body(conj(integer(3), atom(ok)), Original),
    program_with_body(conj(atom(ok), integer(3)), Program),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_reordering_nested_in_conjunction) :-
    program_with_body(
        conj(integer(3), conj(atom(ok), number(4))), Original),
    program_with_body(
        conj(integer(3), conj(number(4), atom(ok))), Program),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_unfold_of_ground_pure_definition) :-
    definition_rewrite_program(integer(3), positive(3), Original),
    definition_rewrite_program(integer(3), integer(3), Program),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_fold_of_ground_pure_definition) :-
    definition_rewrite_program(integer(3), integer(3), Original),
    definition_rewrite_program(integer(3), positive(3), Program),
    definition_rewrite_proof(fold, Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_unfold_with_variable_definition) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                             [mnn_clause(1, positive(X), integer(X),
                                         source(file, 1))],
                             original),
                    mnn_pred(result/0, [], [],
                             [mnn_clause(2, result, positive(3),
                                         source(file, 2))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                            [mnn_clause(1, positive(Y), integer(Y),
                                        source(file, 1))],
                            original),
                   mnn_pred(result/0, [], [],
                            [mnn_clause(2, result, integer(3),
                                        source(file, 2))],
                            original)],
                  proof([]), trace([])),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_unfold_with_impure_definition) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                             [mnn_clause(1, positive(3), write(3),
                                         source(file, 1))],
                             original),
                    mnn_pred(result/0, [], [],
                             [mnn_clause(2, result, positive(3),
                                         source(file, 2))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                            [mnn_clause(1, positive(3), write(3),
                                        source(file, 1))],
                            original),
                   mnn_pred(result/0, [], [],
                            [mnn_clause(2, result, write(3),
                                        source(file, 2))],
                            original)],
                  proof([]), trace([])),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_unfold_with_multiple_definition_clauses) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                             [mnn_clause(1, positive(3), integer(3),
                                         source(file, 1)),
                              mnn_clause(2, positive(4), integer(4),
                                         source(file, 2))],
                             original),
                    mnn_pred(result/0, [], [],
                             [mnn_clause(3, result, positive(3),
                                         source(file, 3))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                            [mnn_clause(1, positive(3), integer(3),
                                        source(file, 1)),
                             mnn_clause(2, positive(4), integer(4),
                                        source(file, 2))],
                            original),
                   mnn_pred(result/0, [], [],
                            [mnn_clause(3, result, integer(3),
                                        source(file, 3))],
                            original)],
                  proof([]), trace([])),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_unfold_rewriting_multiple_occurrences) :-
    definition_rewrite_program(
        integer(3), conj(positive(3), positive(3)), Original),
    definition_rewrite_program(
        integer(3), conj(integer(3), integer(3)), Program),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_fold_into_definition_itself) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                             [mnn_clause(1, positive(3), integer(3),
                                         source(file, 1))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                            [mnn_clause(1, positive(3), positive(3),
                                        source(file, 1))],
                            original)],
                  proof([]), trace([])),
    definition_rewrite_proof(fold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_reordering_with_variable_goals) :-
    program_with_body(conj(integer(X), atom(ok)), Original),
    program_with_body(conj(atom(ok), integer(X)), Program),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_reordering_arbitrary_predicates) :-
    program_with_body(conj(check(value), atom(ok)), Original),
    program_with_body(conj(atom(ok), check(value)), Program),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_program_difference_beyond_one_reordering) :-
    program_with_body(conj(integer(3), atom(ok)), Original),
    program_with_body(conj(atom(changed), integer(3)), Program),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_malformed_program_without_binding_it) :-
    Original = mnn_program(sample, meta(file, []), Predicates,
                           proof([]), trace([])),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(
        Original, Original, Proof, rejected(invalid_or_unsupported_proof)),
    assertion(var(Predicates)).

test(reject_unknown_rule) :-
    Program = mnn_program(sample, meta(file, []), [], proof([]), trace([])),
    Proof = proof([proof_step(1, unfold, [], equivalent)]),
    mnn_proof_checker:check_proof(
        Program, Program, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_unbound_proof_data) :-
    Program = mnn_program(sample, meta(file, []), [], proof([]), trace([])),
    Proof = proof([proof_step(1, identity, [],
                              equivalent(domain(_), modes([])))]),
    mnn_proof_checker:check_proof(
        Program, Program, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_non_program) :-
    identity_proof(Proof),
    mnn_proof_checker:check_proof(not_a_program, not_a_program, Proof,
                                  rejected(invalid_program)).

test(render_identity_proof) :-
    Program = mnn_program(sample, meta(file, []), [], proof([]), trace([])),
    identity_proof(Proof),
    mnn_proof_renderer:render_proof(Program, Program, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, '**Independent check:** accepted.')),
    assertion(sub_string(Markdown, _, _, _, '## Step 1: `identity`')),
    assertion(sub_string(Markdown, _, _, _, 'No program rewrite is claimed.')),
    assertion(sub_string(Markdown, _, _, _, '- Domain: `any`')).

test(render_checked_goal_reordering) :-
    program_with_body(conj(integer(3), atom(ok)), Original),
    program_with_body(conj(atom(ok), integer(3)), Program),
    reorder_proof(Proof),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, '**Independent check:** accepted.')),
    assertion(sub_string(Markdown, _, _, _, '## Step 1: `reorder_goals`')),
    assertion(sub_string(Markdown, _, _, _, 'One adjacent pair')),
    assertion(sub_string(Markdown, _, _, _, 'certifies no other changes')).

test(render_checked_unfold) :-
    definition_rewrite_program(integer(3), positive(3), Original),
    definition_rewrite_program(integer(3), integer(3), Program),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, '## Step 1: `unfold`')),
    assertion(sub_string(Markdown, _, _, _, 'single-clause definition')),
    assertion(sub_string(Markdown, _, _, _, 'pure built-ins')).

test(render_unsupported_proof_as_rejected) :-
    Program = mnn_program(sample, meta(file, []), [], proof([]), trace([])),
    Proof = proof([proof_step(1, unfold, [], equivalent)]),
    mnn_proof_renderer:render_proof(Program, Program, Proof, Markdown),
    assertion(sub_string(
                  Markdown, _, _, _,
                  '**Independent check:** `rejected(invalid_or_unsupported_proof)`.')),
    assertion(sub_string(Markdown, _, _, _, 'proof_step(1,unfold,[],equivalent)')).

test(render_malformed_proof_as_rejected) :-
    Program = mnn_program(sample, meta(file, []), [], proof([]), trace([])),
    Proof = proof([proof_step(1, identity, [], equivalent(domain(_), modes([])))]),
    mnn_proof_renderer:render_proof(Program, Program, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, 'rejected(invalid_or_unsupported_proof)')).

identity_proof(
    proof([proof_step(1, identity, [], equivalent(domain(any), modes([])))])).

reorder_proof(
    proof([proof_step(1, reorder_goals, [],
                      equivalent(domain(any), modes([])))])).

definition_rewrite_proof(Rule,
                         proof([proof_step(1, Rule, [],
                                           equivalent(domain(any),
                                                      modes([])))])).

definition_rewrite_program(DefinitionBody, CallerBody,
                           mnn_program(sample, meta(file, []),
                                       [mnn_pred(positive/1, ['?'], [any],
                                                 [mnn_clause(
                                                      1, positive(3), DefinitionBody,
                                                      source(file, 1))],
                                                 original),
                                        mnn_pred(result/0, [], [],
                                                 [mnn_clause(
                                                      2, result, CallerBody,
                                                      source(file, 2))],
                                                 original)],
                                       proof([]), trace([]))).

program_with_body(Body,
                  mnn_program(sample, meta(file, []),
                              [mnn_pred(sample/1, ['?'], [any],
                                        [mnn_clause(1, sample(_), Body,
                                                    source(file, 1))],
                                        original)],
                              proof([]), trace([]))).

:- end_tests(mnn_proof_checker).

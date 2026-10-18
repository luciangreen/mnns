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
    assertion(sub_string(Markdown, _, _, _, '**Independent check:** `accepted`.')).

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

program_with_body(Body,
                  mnn_program(sample, meta(file, []),
                              [mnn_pred(sample/1, ['?'], [any],
                                        [mnn_clause(1, sample(_), Body,
                                                    source(file, 1))],
                                        original)],
                              proof([]), trace([]))).

:- end_tests(mnn_proof_checker).

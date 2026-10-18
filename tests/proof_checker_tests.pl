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

:- end_tests(mnn_proof_checker).

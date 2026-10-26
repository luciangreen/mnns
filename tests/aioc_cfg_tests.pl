:- begin_tests(mnn_aioc_cfg).

:- use_module('../prolog/aioc/cfg').
:- use_module('../prolog/ir/ir').
:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/runner/sandbox_runner').

test(incorporates_and_independently_checks_cfg, [nondet]) :-
    balanced_grammar(Grammar),
    mnn_aioc_cfg:incorporate_cfg(balanced, Grammar, Program, Proof),
    mnn_proof_checker:check_proof(
        Program, cfg_source(balanced, Grammar), Proof, accepted),
    Program = mnn_program(
        balanced, meta(cfg(balanced), [clause(1), clause(2), clause(3)]),
        [_, mnn_pred(_, _, _, [_, _], _)], proof([]), trace([])).

test(emitted_cfg_runs_in_bounded_sandbox, [nondet]) :-
    balanced_grammar(Grammar),
    mnn_aioc_cfg:incorporate_cfg(balanced, Grammar, Program, _),
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(
              Source, balanced([]), [], answers([[]])),
          mnn_sandbox_runner:run_program(
              Source, balanced([a,b]), [], answers([[]])),
          mnn_sandbox_runner:run_program(
              Source, balanced([a,a,b,b]), [], answers([[]])),
          mnn_sandbox_runner:run_program(
              Source, balanced([a,b,b]), [], answers([]))
        ),
        ( catch(close(Stream), _, true),
          catch(delete_file(Source), _, true)
        )).

test(preserves_production_order_and_duplicate_answers, [nondet]) :-
    Grammar = cfg(s, [rule(s, [terminal(b)]),
                      rule(s, [terminal(a)]),
                      rule(s, [terminal(a)])]),
    mnn_aioc_cfg:incorporate_cfg(ordered_cfg, Grammar, Program, _),
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(
              Source, ordered_cfg(_Tokens), [], answers([[[b]], [[a]], [[a]]]))
        ),
        ( catch(close(Stream), _, true),
          catch(delete_file(Source), _, true)
        )).

test(checker_rejects_noncanonical_cfg_translation, [nondet]) :-
    balanced_grammar(Grammar),
    mnn_aioc_cfg:incorporate_cfg(balanced, Grammar, Program, Proof),
    copy_term(Program, Changed),
    Changed = mnn_program(_, _, [Wrapper|_], _, _),
    Wrapper = mnn_pred(_, _, _, [Clause], _),
    setarg(3, Clause, true),
    mnn_proof_checker:check_proof(
        Changed, cfg_source(balanced, Grammar), Proof,
        rejected(invalid_or_unsupported_proof)).

test(rejects_unbound_proof_without_instantiating_it, [nondet]) :-
    balanced_grammar(Grammar),
    mnn_aioc_cfg:incorporate_cfg(balanced, Grammar, Program, _),
    Proof = _,
    mnn_proof_checker:check_proof(
        Program, cfg_source(balanced, Grammar), Proof,
        rejected(invalid_or_unsupported_proof)),
    assertion(var(Proof)).

test(rejects_untrusted_rule_body,
     [throws(error(domain_error(cfg_source, _), _))]) :-
    mnn_aioc_cfg:incorporate_cfg(
        unsafe, cfg(start, [rule(start, [call(write(executed))])]), _, _).

test(rejects_undefined_nonterminal,
     [throws(error(domain_error(cfg_source, _), _))]) :-
    mnn_aioc_cfg:incorporate_cfg(
        bad, cfg(start, [rule(start, [nonterminal(missing)])]), _, _).

test(rejects_non_ground_terminal,
     [throws(error(domain_error(cfg_source, _), _))]) :-
    mnn_aioc_cfg:incorporate_cfg(
        bad, cfg(start, [rule(start, [terminal(_Token)])]), _, _).

balanced_grammar(
    cfg(s, [ rule(s, [terminal(a), nonterminal(s), terminal(b)]),
             rule(s, [])
           ])).

:- end_tests(mnn_aioc_cfg).

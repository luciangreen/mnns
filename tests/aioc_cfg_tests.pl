:- begin_tests(mnn_aioc_cfg).

:- use_module('../prolog/aioc/cfg').
:- use_module('../prolog/ir/ir').
:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/runner/sandbox_runner').

test(cfg_translation_is_independently_checked) :-
    sentence_cfg(Grammar),
    mnn_aioc_cfg:incorporate_cfg(grammar, Grammar, Program, Proof),
    mnn_proof_checker:check_proof(
        Program, cfg_source(grammar, Grammar), Proof, accepted),
    Program = mnn_program(
                  grammar, meta(cfg(grammar, sentence),
                                [clause(1), clause(2), clause(3), clause(4)]),
                  [mnn_pred(sentence/2, ['?', '?'], [any, any], _, original),
                   mnn_pred(noun/2, ['?', '?'], [any, any], _, original),
                   mnn_pred(verb/2, ['?', '?'], [any, any], _, original)],
                  proof([]), trace([])).

test(cfg_generated_program_runs_in_sandbox, [nondet]) :-
    sentence_cfg(Grammar),
    mnn_aioc_cfg:incorporate_cfg(grammar, Grammar, Program, _),
    run_emitted_program(
        Program,
        [ run(sentence([cat, sleeps], []), [], answers([[]])),
          run(sentence([dog, sleeps], []), [], answers([[]])),
          run(sentence([bird, sleeps], []), [], answers([]))
        ]).

test(recursive_cfg_supports_epsilon_productions, [nondet]) :-
    Grammar = cfg(s, [rule(s, [terminal(a), nonterminal(s)]), rule(s, [])]),
    mnn_aioc_cfg:incorporate_cfg(recursive, Grammar, Program, _),
    run_emitted_program(
        Program,
        [ run(s([a, a], []), [], answers([[]])),
          run(s([], []), [], answers([[]])),
          run(s([b], []), [], answers([]))
        ]).

test(dcg_translation_is_independently_checked) :-
    Grammar = dcg(word,
                  [dcg_rule(word, [terminal(hello), nonterminal(noun)]),
                   dcg_rule(noun, [terminal(world)])]),
    mnn_aioc_cfg:incorporate_dcg(grammar, Grammar, Program, Proof),
    mnn_proof_checker:check_proof(
        Program, dcg_source(grammar, Grammar), Proof, accepted),
    Program = mnn_program(grammar, meta(dcg(grammar, word), _), _, _, _).

test(dcg_generated_program_runs_in_sandbox, [nondet]) :-
    Grammar = dcg(word,
                  [dcg_rule(word, [terminal(hello), nonterminal(noun)]),
                   dcg_rule(noun, [terminal(world)])]),
    mnn_aioc_cfg:incorporate_dcg(grammar, Grammar, Program, _),
    run_emitted_program(
        Program,
        [ run(word([hello, world], []), [], answers([[]])),
          run(word([hello, there], []), [], answers([]))
        ]).

test(checker_rejects_changed_cfg_translation) :-
    Grammar = cfg(s, [rule(s, [terminal(a)])]),
    mnn_aioc_cfg:incorporate_cfg(grammar, Grammar, Program, Proof),
    copy_term(Program, Changed),
    Changed = mnn_program(_, _, [Predicate], _, _),
    setarg(1, Predicate, other/2),
    mnn_proof_checker:check_proof(
        Changed, cfg_source(grammar, Grammar), Proof,
        rejected(invalid_or_unsupported_proof)).

test(rejects_undefined_nonterminal,
     [throws(error(domain_error(cfg_grammar, _), _))]) :-
    mnn_aioc_cfg:incorporate_cfg(
        grammar, cfg(s, [rule(s, [nonterminal(missing)])]), _, _).

test(rejects_unbound_terminal,
     [throws(error(domain_error(cfg_grammar, _), _))]) :-
    Token = _,
    mnn_aioc_cfg:incorporate_cfg(
        grammar, cfg(s, [rule(s, [terminal(Token)])]), _, _).

test(rejects_system_predicate_as_nonterminal,
     [throws(error(domain_error(cfg_grammar, _), _))]) :-
    mnn_aioc_cfg:incorporate_cfg(
        grammar, cfg(is, [rule(is, [])]), _, _).

test(rejects_list_functor_as_nonterminal,
     [throws(error(domain_error(cfg_grammar, _), _))]) :-
    mnn_aioc_cfg:incorporate_cfg(
        grammar, cfg('.', [rule('.', [])]), _, _).

sentence_cfg(
    cfg(sentence,
        [rule(sentence, [nonterminal(noun), nonterminal(verb)]),
         rule(noun, [terminal(cat)]),
         rule(noun, [terminal(dog)]),
         rule(verb, [terminal(sleeps)])])).

run_emitted_program(Program, Calls) :-
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Source),
          maplist(run_source_call(Source), Calls)
        ),
        ( catch(close(Stream), _, true),
          catch(delete_file(Source), _, true)
        )).

run_source_call(Source, run(Query, Options, Expected)) :-
    mnn_sandbox_runner:run_program(Source, Query, Options, Expected).

:- end_tests(mnn_aioc_cfg).

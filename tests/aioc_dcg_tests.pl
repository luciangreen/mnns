:- begin_tests(mnn_aioc_dcg).

:- use_module('../prolog/aioc/dcg').
:- use_module('../prolog/ir/ir').
:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/runner/sandbox_runner').

test(incorporates_and_independently_checks_dcg_data, [nondet]) :-
    DCG = dcg(s, [ (s --> [a], item, [b]),
                   (item --> [x])
                 ]),
    mnn_aioc_dcg:incorporate_dcg(parser, DCG, Program, Proof),
    mnn_proof_checker:check_proof(
        Program, dcg_source(parser, DCG), Proof, accepted),
    Program = mnn_program(
        parser, meta(dcg(parser), [clause(1), clause(2), clause(3)]), _, _, _).

test(emitted_dcg_runs_in_bounded_sandbox, [nondet]) :-
    DCG = dcg(s, [ (s --> [a], item, [b]),
                   (item --> [x])
                 ]),
    mnn_aioc_dcg:incorporate_dcg(parser, DCG, Program, _),
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(
              Source, parser([a,x,b]), [], answers([[]])),
          mnn_sandbox_runner:run_program(
              Source, parser([a,b]), [], answers([]))
        ),
        ( catch(close(Stream), _, true),
          catch(delete_file(Source), _, true)
        )).

test(preserves_alternative_order_and_duplicate_answers, [nondet]) :-
    DCG = dcg(s, [s --> ([a] ; [b] ; [a])]),
    mnn_aioc_dcg:incorporate_dcg(alternatives, DCG, Program, _),
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(
              Source, alternatives(_Tokens), [], answers([[[a]], [[b]], [[a]]]))
        ),
        ( catch(close(Stream), _, true),
          catch(delete_file(Source), _, true)
        )).

test(checker_rejects_noncanonical_dcg_translation, [nondet]) :-
    DCG = dcg(s, [s --> [a]]),
    mnn_aioc_dcg:incorporate_dcg(parser, DCG, Program, Proof),
    copy_term(Program, Changed),
    Changed = mnn_program(_, _, [Wrapper|_], _, _),
    Wrapper = mnn_pred(_, _, _, [Clause], _),
    setarg(3, Clause, true),
    mnn_proof_checker:check_proof(
        Changed, dcg_source(parser, DCG), Proof,
        rejected(invalid_or_unsupported_proof)).

test(rejects_unsupported_braced_goal,
     [throws(error(domain_error(dcg_source, _), _))]) :-
    DCG = dcg(s, [s --> {write(executed)}]),
    mnn_aioc_dcg:incorporate_dcg(parser, DCG, _, _).

test(rejects_undefined_nonterminal,
     [throws(error(domain_error(dcg_source, _), _))]) :-
    DCG = dcg(s, [s --> missing]),
    mnn_aioc_dcg:incorporate_dcg(parser, DCG, _, _).

test(rejects_non_ground_terminal,
     [throws(error(domain_error(dcg_source, _), _))]) :-
    DCG = dcg(s, [s --> [_Token]]),
    mnn_aioc_dcg:incorporate_dcg(parser, DCG, _, _).

:- end_tests(mnn_aioc_dcg).

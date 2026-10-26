:- begin_tests(mnn_aioc_dtree).

:- use_module('../prolog/aioc/dtree').
:- use_module('../prolog/ir/ir').
:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/runner/sandbox_runner').

test(incorporates_and_proves_a_data_only_decision_tree) :-
    classification_tree(Input, Tree),
    mnn_aioc_dtree:incorporate_dtree(
        classify, Input, Tree, Program, Proof),
    Source = dtree_source(classify, Input, Tree),
    mnn_proof_checker:check_proof(Program, Source, Proof, accepted),
    Head =.. [classify, Input, Output],
    Program = mnn_program(
                  classify, meta(dtree(classify), [clause(1)]),
                  [mnn_pred(
                       classify/2, ['?', '?'], [any, any],
                       [mnn_clause(1, Head,
                                   ite(integer(Input),
                                       ite(Input < 0, Output = negative,
                                           ite(Input =:= 0, Output = zero,
                                               Output = positive)),
                                       Output = non_integer),
                                   source(dtree(classify), 1))],
                       original)],
                  proof([]), trace([])).

test(emitted_tree_runs_through_the_bounded_sandbox, [nondet]) :-
    classification_tree(Input, Tree),
    mnn_aioc_dtree:incorporate_dtree(
        classify, Input, Tree, Program, _),
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        (         close(Stream),
          mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(
              Source, classify(-2, _Negative), [], answers([[negative]])),
          mnn_sandbox_runner:run_program(
              Source, classify(0, _Zero), [], answers([[zero]])),
          mnn_sandbox_runner:run_program(
              Source, classify(4, _Positive), [], answers([[positive]])),
          mnn_sandbox_runner:run_program(
              Source, classify(no, _Other), [], answers([[non_integer]]))
        ),
        ( catch(close(Stream), _, true),
          catch(delete_file(Source), _, true)
        )).

test(checker_rejects_a_changed_tree_translation) :-
    classification_tree(Input, Tree),
    mnn_aioc_dtree:incorporate_dtree(
        classify, Input, Tree, Program, Proof),
    Source = dtree_source(classify, Input, Tree),
    copy_term(Program, Changed),
    Changed = mnn_program(_, _, [Predicate], _, _),
    setarg(1, Predicate, other/2),
    mnn_proof_checker:check_proof(
        Changed, Source, Proof, rejected(invalid_or_unsupported_proof)).

test(checker_rejects_unbound_proof_without_instantiating_it) :-
    classification_tree(Input, Tree),
    mnn_aioc_dtree:incorporate_dtree(
        classify, Input, Tree, Program, _),
    Proof = _,
    mnn_proof_checker:check_proof(
        Program, dtree_source(classify, Input, Tree), Proof,
        rejected(invalid_or_unsupported_proof)),
    assertion(var(Proof)).

test(rejects_non_whitelisted_tree_test, [throws(error(domain_error(dtree_source, _), _))]) :-
    Input = _,
    mnn_aioc_dtree:incorporate_dtree(
        classify, Input, dtree(write(executed), leaf(yes), leaf(no)), _, _).

test(rejects_leaf_variables_other_than_the_input,
     [throws(error(domain_error(dtree_source, _), _))]) :-
    Input = _,
    Value = _,
    mnn_aioc_dtree:incorporate_dtree(
        classify, Input,
        dtree(integer(Input), leaf(Value), leaf(no)), _, _).

test(rejects_a_nonvariable_input,
     [throws(error(type_error(variable, 1), _))]) :-
    mnn_aioc_dtree:incorporate_dtree(
        classify, 1, leaf(yes), _, _).

classification_tree(Input,
                   dtree(integer(Input),
                         dtree(Input < 0,
                               leaf(negative),
                               dtree(Input =:= 0,
                                     leaf(zero),
                                     leaf(positive))),
                         leaf(non_integer))).

:- end_tests(mnn_aioc_dtree).

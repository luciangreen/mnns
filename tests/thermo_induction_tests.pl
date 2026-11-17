:- begin_tests(mnn_thermo_induction).

:- use_module('../prolog/thermo/thermo').
:- use_module('../prolog/thermo/thermo_induction').
:- use_module('../prolog/aioc/thermo').
:- use_module('../prolog/aioc/library').
:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/ir/ir').
:- use_module('../prolog/runner/sandbox_runner').
:- use_module(library(filesex)).

% ---- the induction proof ----

test(induction_proof_is_accepted) :-
    mnn_thermo_induction:thermo_induction_proof(P),
    mnn_thermo_induction:thermo_check_induction(P, R),
    assertion(R == accepted).

test(wrong_pascal_term_is_rejected) :-
    tampered(1, proof_step(1, pascal_term, [def(m), fact_rec(n), fact_rec(cj)],
                           forall([c, j], implies(and(n >= 1, cj >= 1),
                                                  eq(m(c_minus_j) * n, m(c))))),
             R),
    assertion(R == rejected(1, pascal_term)).

test(pascal_term_needs_both_factorial_rules) :-
    tampered(1, proof_step(1, pascal_term, [def(m), fact_rec(n)],
                           forall([c, j], implies(and(n >= 1, cj >= 1),
                                                  eq(m(c_minus_j) * n, m(c) * cj)))),
             R),
    assertion(R == rejected(1, pascal_term)).

test(wrong_pascal_sum_is_rejected) :-
    tampered(2, proof_step(2, pascal_sum, [linearity, def(n)],
                           forall([c], implies(n >= 1,
                                               eq(sum_j(m(c) * cj * cj / n), m(c))))),
             R),
    assertion(R == rejected(2, pascal_sum)).

test(pascal_sum_needs_linearity) :-
    tampered(2, proof_step(2, pascal_sum, [def(n)],
                           forall([c], implies(n >= 1,
                                               eq(sum_j(m(c) * cj / n), m(c))))),
             R),
    assertion(R == rejected(2, pascal_sum)).

test(wrong_base_case_is_rejected) :-
    mnn_thermo_induction:thermo_induction_proof(proof(Steps)),
    nth1(4, Steps, proof_step(4, base_case, Ps,
                              forall([c], implies(n =:= 0, and(eq(_, _), B))))),
    tampered(4, proof_step(4, base_case, Ps,
                           forall([c], implies(n =:= 0, and(eq(m(zeros), 2), B)))),
             R),
    assertion(R == rejected(4, base_case)).

test(induction_without_its_base_case_is_rejected) :-
    tampered(7, proof_step(7, induction, [step(6)],
                           forall([c], bijection(rank, class(c), interval(0, m(c))))),
             R),
    assertion(R == rejected(7, induction)).

test(steps_out_of_order_are_rejected) :-
    mnn_thermo_induction:thermo_induction_proof(proof([S1, S2|Rest])),
    mnn_thermo_induction:thermo_check_induction(proof([S2, S1|Rest]), R),
    assertion(R == rejected(1, malformed_step)).

test(proof_missing_its_last_step_is_rejected) :-
    mnn_thermo_induction:thermo_induction_proof(proof(Steps)),
    once(append(Front, [_], Steps)),
    mnn_thermo_induction:thermo_check_induction(proof(Front), R),
    assertion(R == rejected(end, missing_conclusion)).

test(not_a_proof_is_rejected) :-
    mnn_thermo_induction:thermo_check_induction(proof([]), R),
    assertion(R == rejected(0, not_a_proof)).

% ---- incorporation ----

test(banana_class_is_incorporated_and_proved) :-
    mnn_aioc_thermo:incorporate_thermo(banana, [a,b,n], [3,1,2], Program, Proof),
    mnn_proof_checker:check_proof(Program, thermo_source(banana, [a,b,n], [3,1,2]),
                                  Proof, accepted),
    Program = mnn_program(banana, meta(thermo(banana), Ids),
                          [mnn_pred(banana/2, _, _, Clauses, original)], _, _),
    length(Clauses, 60),
    length(Ids, 60),
    nth1(35, Clauses, mnn_clause(35, banana(34, Seq), true, _)),
    assertion(Seq == [b,a,n,a,n,a]).

test(changed_table_is_rejected) :-
    mnn_aioc_thermo:incorporate_thermo(t, [a,b], [2,1], Program, Proof),
    Program = mnn_program(N, Meta, [mnn_pred(PI, Ms, Ts, [C1, C2|Cs], O)], P, T),
    C1 = mnn_clause(1, t(0, S1), true, Src1),
    C2 = mnn_clause(2, t(1, S2), true, Src2),
    Swapped = mnn_program(N, Meta, [mnn_pred(PI, Ms, Ts,
                                             [mnn_clause(1, t(0, S2), true, Src1),
                                              mnn_clause(2, t(1, S1), true, Src2)|Cs],
                                             O)], P, T),
    mnn_proof_checker:check_proof(Swapped, thermo_source(t, [a,b], [2,1]), Proof, R),
    assertion(R = rejected(_)).

test(incorporation_without_the_induction_is_rejected) :-
    mnn_aioc_thermo:incorporate_thermo(t, [a,b], [2,1], Program, _),
    Proof = proof([proof_step(1, incorporate_thermo, [],
                              equivalent(domain(type_class([a,b], [2,1])), modes(all)))]),
    mnn_proof_checker:check_proof(Program, thermo_source(t, [a,b], [2,1]), Proof, R),
    assertion(R = rejected(_)).

test(unsorted_alphabet_is_not_incorporated,
     [error(domain_error(thermo_source, _))]) :-
    mnn_aioc_thermo:incorporate_thermo(t, [b,a], [1,1], _, _).

test(too_large_class_is_not_incorporated,
     [error(domain_error(thermo_source, _))]) :-
    mnn_aioc_thermo:incorporate_thermo(t, [a,b,c,d,e], [2,2,2,2,2], _, _).

test(table_runs_both_ways_in_the_sandbox, [nondet]) :-
    mnn_aioc_thermo:incorporate_thermo(banana, [a,b,n], [3,1,2], Program, _),
    setup_call_cleanup(
        tmp_file_stream(text, Source, Stream),
        ( close(Stream),
          mnn_ir:emit_program(Program, Source),
          mnn_sandbox_runner:run_program(Source, banana(34, _S), [],
                                         answers([[[b,a,n,a,n,a]]])),
          mnn_sandbox_runner:run_program(Source, banana(_R, [b,a,n,a,n,a]), [],
                                         answers([[34]]))
        ),
        delete_file(Source)).

test(incorporated_class_is_stored_in_the_aioc_library) :-
    mnn_aioc_thermo:incorporate_thermo(ab, [a,b], [2,2], Program, Proof),
    Source = thermo_source(ab, [a,b], [2,2]),
    Entry = mnn_library_entry(ab, Program, Source, Proof,
                              assessment(accepted, recorded),
                              cost(steps(1)), cycle(1), thermo,
                              [test_result(full_suite, passed)]),
    tmp_file(mnn_thermo_library, Directory),
    make_directory(Directory),
    setup_call_cleanup(
        true,
        ( mnn_aioc_library:store_entry(Directory, Entry),
          mnn_aioc_library:get_entry(Directory, ab,
              accepted(mnn_library_entry(ab, Stored, StoredSource, _, _, _, _, _, _))),
          assertion(Stored =@= Program),
          assertion(StoredSource == Source)
        ),
        delete_directory_and_contents(Directory)).

tampered(N, Step, R) :-
    mnn_thermo_induction:thermo_induction_proof(proof(Steps)),
    nth1(N, Steps, _, Rest),
    nth1(N, Steps1, Step, Rest),
    mnn_thermo_induction:thermo_check_induction(proof(Steps1), R).

:- end_tests(mnn_thermo_induction).

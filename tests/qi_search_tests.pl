:- begin_tests(mnn_qi_search).

:- use_module('../prolog/quantum/qi_search').
:- use_module('../prolog/plop/plop').
:- use_module('../prolog/proof/proof_checker').
:- use_module(library(filesex)).
:- use_module(library(readutil)).

test(search_is_reproducible_and_returns_a_checked_candidate) :-
    findall_program(Program),
    Options = [seed(17), links([qi_link(values/1, num/1)])],
    mnn_qi_search:qi_search(Program, Options, Best1, Report1),
    mnn_qi_search:qi_search(Program, Options, Best2, Report2),
    assertion(Best1 =@= Best2),
    assertion(Report1 =@= Report2),
    assertion(Report1 = qi_report(
                          17, [qi_link(values/1, num/1)], Candidates,
                          History, selected(_), _, proof_steps(_),
                          rewrites_tried(3))),
    assertion(once(member(candidate(original, _, _, _, _), Candidates))),
    assertion(once(member(event(
                                    predicate_values_1, proposal(_), accepted,
                                    _, _, _, _, linked_rechecks(
                                                   [linked_recheck(num/1, accepted)]),
                                    _),
                                History))),
    (   Best1 =@= Program
    ->  identity_proof(Proof)
    ;   mnn_plop:optimize_program(
            Program, Best1, plop_report(_, Proof, accepted))
    ),
    once(mnn_proof_checker:check_proof(Best1, Program, Proof, accepted)).

test(unsupported_program_keeps_the_original) :-
    unsupported_program(Program),
    mnn_qi_search:qi_search(Program, [], Best,
                            qi_report(0, [], [_], History,
                                      selected(original), _, proof_steps(1),
                                      rewrites_tried(2))),
    assertion(Best =@= Program),
    assertion(once(member(event(whole_program, proposal(_), accepted,
                                attenuated, _, _, _, _, _), History))).

test(exports_schematic_openqasm_selection_register) :-
    findall_program(Program),
    temporary_qasm_file(File),
    setup_call_cleanup(
        true,
        ( mnn_qi_search:qi_export(Program, qasm, File),
          read_file_to_string(File, Qasm, []),
          assertion(sub_string(Qasm, _, _, _, "OPENQASM 3.0;")),
          assertion(sub_string(Qasm, _, _, _, "qubit[2] q;")),
          assertion(sub_string(Qasm, _, _, _, "measure q[1] -> c[1];"))
        ),
        delete_file(File)).

test(rejects_links_to_unknown_predicates,
     [throws(error(domain_error(qi_link, qi_link(missing/0, num/1)), _))]) :-
    findall_program(Program),
    mnn_qi_search:qi_search(
        Program, [links([qi_link(missing/0, num/1)])], _, _).

test(rejects_negative_seed,
     [throws(error(domain_error(not_less_than_zero, -1), _))]) :-
    findall_program(Program),
    mnn_qi_search:qi_search(Program, [seed(-1)], _, _).

temporary_qasm_file(File) :-
    tmp_file(mnn_qi_search, Base),
    atom_concat(Base, '.qasm', File).

findall_program(
    mnn_program(
        sample,
        meta(source, [clause(1), clause(2), clause(3)]),
        [mnn_pred(num/1, ['?'], [any],
                  [mnn_clause(1, num(1), true, source(test, 1)),
                   mnn_clause(2, num(2), true, source(test, 2))],
                  original),
         mnn_pred(values/1, ['?'], [any],
                  [mnn_clause(3, values(Values),
                              findall(X, num(X), Values), source(test, 3))],
                  original)],
        proof([]), trace([]))).

unsupported_program(
    mnn_program(
        sample,
        meta(source, [clause(1)]),
        [mnn_pred(values/1, ['?'], [any],
                  [mnn_clause(1, values(Values),
                              findall(X, arbitrary_generator(X), Values),
                              source(test, 1))],
                  original)],
        proof([]), trace([]))).

identity_proof(
    proof([proof_step(1, identity, [],
                      equivalent(domain(all), modes(all)))])).

:- end_tests(mnn_qi_search).

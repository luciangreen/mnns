:- begin_tests(mnn_proof_checker).

:- use_module('../prolog/proof/proof_checker').
:- use_module('../prolog/proof/proof_renderer').
:- use_module('../prolog/loop2/loop2').

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

test(accept_ground_pure_definition_introduction) :-
    definition_introduction_program(Original, Program),
    definition_introduction_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_unary_variable_definition_introduction) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(sample/1, ['?'], [any],
                             [mnn_clause(1, sample(X),
                                         conj(integer(X), check(X)),
                                         source(file, 1))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(sample/1, ['?'], [any],
                            [mnn_clause(1, sample(Y),
                                        conj(mnn_definition_1(Y), check(Y)),
                                        source(file, 1))],
                            original),
                   mnn_pred(mnn_definition_1/1, ['?'], [any],
                            [mnn_clause(2, mnn_definition_1(Z), integer(Z),
                                        source(generated, 0))],
                            introduced)],
                  proof([]), trace([])),
    definition_introduction_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_multi_variable_definition_introduction) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(sample/2, ['?', '?'], [any, any],
                             [mnn_clause(1, sample(X, Y),
                                         conj(integer(X), atom(Y)),
                                         source(file, 1))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(sample/2, ['?', '?'], [any, any],
                            [mnn_clause(1, sample(A, B),
                                        mnn_definition_1(A, B),
                                        source(file, 1))],
                            original),
                   mnn_pred(mnn_definition_1/2, ['?', '?'], [any, any],
                            [mnn_clause(2, mnn_definition_1(C, D),
                                        conj(integer(C), atom(D)),
                                        source(generated, 0))],
                            introduced)],
                  proof([]), trace([])),
    definition_introduction_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_definition_introduction_in_proof_sequence) :-
    definition_introduction_program(Original, Program),
    Proof = proof([
        proof_step(1, introduce_definition, [],
                   equivalent(domain(any), modes([]))),
        proof_step(2, identity, [],
                   equivalent(domain(any), modes([])))
    ]),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_direct_ground_member_findall_to_fold) :-
    findall_to_fold_programs(Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_nth0_index_findall_to_fold) :-
    nth0_findall_to_fold_programs([a, b, a], Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_nth0_index_findall_to_fold_on_empty_list) :-
    nth0_findall_to_fold_programs([], Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_nth1_index_findall_to_fold) :-
    nth1_findall_to_fold_programs([a, b, a], Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_nth1_index_findall_to_fold_on_empty_list) :-
    nth1_findall_to_fold_programs([], Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_length_findall_to_fold) :-
    length_findall_to_fold_programs(
        _, [a, b], Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [2]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_length_findall_to_fold_on_empty_list) :-
    length_findall_to_fold_programs(_, [], Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [0]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_length_findall_to_fold_with_bound_length) :-
    length_findall_to_fold_programs(2, [a, b], Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_length_findall_to_fold_with_mismatched_length) :-
    length_findall_to_fold_programs(3, [a, b], Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == []),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_length_findall_to_fold_with_arithmetic_filter) :-
    filtered_length_findall_to_fold_programs(
        Length, Length, [a, b], Length > 1, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [2]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_filtered_length_findall_to_fold_with_changed_values) :-
    filtered_length_findall_to_fold_programs(
        Length, Length, [a, b], Length > 1, Original, Program0),
    replace_loop_values(Program0, [changed], Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_length_findall_to_fold_with_changed_values) :-
    length_findall_to_fold_programs(
        _, [a, b], Original, Program0),
    replace_loop_values(Program0, [changed], Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_bounded_between_findall_to_fold) :-
    between_findall_to_fold_programs(2, 4, Value, Value, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [2, 3, 4]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_bounded_between_findall_to_fold_with_bound_value) :-
    between_findall_to_fold_programs(2, 4, 3, 3, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [3]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_bounded_between_findall_to_fold_with_arithmetic_filters) :-
    filtered_between_findall_to_fold_programs(
        Value,
        conj(Value > 2, Value =< 4), Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [3, 4]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_filtered_between_findall_to_fold_with_changed_values) :-
    filtered_between_findall_to_fold_programs(
        Value,
        Value > 2, Original, Program0),
    replace_loop_values(Program0, [3], Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_between_findall_to_fold_with_unsupported_filter) :-
    filtered_between_findall_to_fold_programs(
        Value,
        member(Value, [2, 4]), Original, Program),
    assertion(Program =@= Original),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_ground_fact_findall_to_fold_preserving_patterns_and_duplicates) :-
    fact_findall_to_fold_programs(Value, pair(a, Value), Original, Program),
    Program = mnn_program(_, _,
                          [_, mnn_pred(_, _, _,
                                       [mnn_clause(_, _, mnn_loop2_1(Values, _),
                                                   _)],
                                       _)|_],
                          _, _),
    assertion(Values == [1, 1]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_fact_findall_to_fold_with_arithmetic_filter) :-
    Original = mnn_program(
                   sample,
                   meta(source, [clause(1), clause(2), clause(3), clause(4)]),
                   [mnn_pred(pair/2, ['?', '?'], [any, any],
                             [mnn_clause(1, pair(a, 1), true, source(source, 1)),
                              mnn_clause(2, pair(b, 2), true, source(source, 2)),
                              mnn_clause(3, pair(a, 3), true, source(source, 3))],
                             original),
                    mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(
                                  4, numbers(Results),
                                  findall(Value,
                                          conj(pair(a, Value), Value > 1),
                                          Results),
                                  source(source, 4))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _),
    Program = mnn_program(_, _,
                          [_, mnn_pred(_, _, _,
                                       [mnn_clause(_, _, mnn_loop2_1(Values, _),
                                                   _)],
                                       _)|_],
                          _, _),
    assertion(Values == [3]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_ground_fact_findall_to_fold_with_changed_values) :-
    fact_findall_to_fold_programs(Value, pair(a, Value), Original, Program0),
    Program0 = mnn_program(Name, Meta,
                           [Facts, Predicate, Helper], ProofData, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                          [mnn_clause(4, numbers(Results),
                                      mnn_loop2_1([1, 1], Results), Source)],
                          Status),
    Program = mnn_program(
                  Name, Meta,
                  [Facts,
                   mnn_pred(numbers/1, Modes, Domains,
                            [mnn_clause(4, numbers(Results),
                                        mnn_loop2_1([1], Results), Source)],
                            Status),
                   Helper],
                  ProofData, Trace),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_finite_acyclic_rule_findall_to_fold) :-
    rule_findall_to_fold_programs(Original, Program),
    Program = mnn_program(_, _,
                          [_, _, mnn_pred(_, _, _,
                                          [mnn_clause(_, _, mnn_loop2_1(Values, _),
                                                      _)],
                                          _)|_],
                          _, _),
    assertion(Values == [2, 2, 0]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_rule_findall_to_fold_with_changed_values) :-
    rule_findall_to_fold_programs(Original, Program0),
    Program0 = mnn_program(Name, Meta,
                           [Numbers, Positive,
                            mnn_pred(Key, Modes, Domains,
                                     [mnn_clause(Id, Head, LoopCall, Location)],
                                     Status),
                            Helper],
                           ProofData, Trace),
    LoopCall = mnn_loop2_1(_, Results),
    Program = mnn_program(
                  Name, Meta,
                  [Numbers, Positive,
                   mnn_pred(Key, Modes, Domains,
                            [mnn_clause(Id, Head,
                                        mnn_loop2_1([2, 3, 0], Results),
                                        Location)],
                            Status),
                   Helper],
                  ProofData, Trace),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_recursive_rule_findall_to_fold) :-
    rule_findall_to_fold_programs(Original0, Program),
    Original0 = mnn_program(Name, Meta,
                            [Numbers, mnn_pred(positive/1, Modes, Domains,
                                               [mnn_clause(4, positive(Value),
                                                           _,
                                                           Source),
                                                Fact],
                                               Status),
                             Results],
                            ProofData, Trace),
    Original = mnn_program(
                   Name, Meta,
                   [Numbers,
                    mnn_pred(positive/1, Modes, Domains,
                             [mnn_clause(4, positive(Value), positive(Value),
                                         Source),
                              Fact],
                             Status),
                    Results],
                   ProofData, Trace),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_non_ground_fact_generator_findall_to_fold) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1), clause(2)]),
                   [mnn_pred(pair/2, ['?', '?'], [any, any],
                             [mnn_clause(1, pair(a, _), true, source(source, 1))],
                             original),
                    mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(2, numbers(Results),
                                         findall(Value, pair(a, Value), Results),
                                         source(source, 2))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, loop2_report([])),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_reversed_between_findall_to_fold_as_empty) :-
    between_findall_to_fold_programs(4, 2, Value, Value, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == []),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_oversized_between_findall_to_fold) :-
    between_findall_to_fold_programs(0, 10000, _, _, Original, Program),
    assertion(Program =@= Original),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_between_findall_to_fold_with_changed_values) :-
    between_findall_to_fold_programs(2, 4, Value, Value, Original, Program0),
    Program0 = mnn_program(Name, Meta, [Predicate, Helper], ProofData, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                          [mnn_clause(1, numbers(Results),
                                      mnn_loop2_1([2, 3, 4], Results), Source)],
                          Status),
    Program = mnn_program(
                  Name, Meta,
                  [mnn_pred(numbers/1, Modes, Domains,
                            [mnn_clause(1, numbers(Results),
                                        mnn_loop2_1([2, 4], Results), Source)],
                            Status),
                   Helper],
                  ProofData, Trace),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_ground_select_findall_to_fold_preserving_order_and_duplicates) :-
    List = [a, b, a],
    Template = pair(Value, Rest),
    Generator = select(Value, List, Rest),
    select_findall_to_fold_programs(Template, Generator, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [pair(a, [b, a]), pair(b, [a, a]),
                         pair(a, [a, b])]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_select_findall_to_fold_with_pattern) :-
    List = [a, b, a],
    Template = Rest,
    Generator = select(a, List, Rest),
    select_findall_to_fold_programs(Template, Generator, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [[b, a], [a, b]]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(accept_ground_select_findall_to_fold_with_arithmetic_filter) :-
    List = [1, 2, 1, 3],
    Template = pair(Value, Rest),
    Generator = conj(select(Value, List, Rest), Value =\= 2),
    select_findall_to_fold_programs(Template, Generator, Original, Program),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _), _)],
                                    _)|_],
                          _, _),
    assertion(Values == [pair(1, [2, 1, 3]), pair(1, [1, 2, 3]),
                         pair(3, [1, 2, 1])]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_ground_select_findall_to_fold_with_unsupported_filter) :-
    List = [1, 2, 3],
    Template = pair(Value, Rest),
    Generator = conj(select(Value, List, Rest), Value \= 2),
    select_findall_to_fold_programs(Template, Generator, Original, Program),
    assertion(Program =@= Original),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_ground_select_findall_to_fold_with_changed_filtered_values) :-
    List = [1, 2, 1, 3],
    Template = pair(Value, Rest),
    Generator = conj(select(Value, List, Rest), Value =\= 2),
    select_findall_to_fold_programs(Template, Generator, Original, Program0),
    Program0 = mnn_program(Name, Meta, [Predicate, Helper], ProofData, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                          [mnn_clause(1, numbers(Results),
                                      mnn_loop2_1(Values, Results), Source)],
                          Status),
    assertion(Values == [pair(1, [2, 1, 3]), pair(1, [1, 2, 3]),
                         pair(3, [1, 2, 1])]),
    Program = mnn_program(
                  Name, Meta,
                  [mnn_pred(numbers/1, Modes, Domains,
                            [mnn_clause(1, numbers(Results),
                                        mnn_loop2_1([pair(1, [2, 1, 3]),
                                                     pair(3, [1, 2, 1])],
                                                    Results),
                                        Source)],
                            Status),
                   Helper],
                  ProofData, Trace),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_ground_select_findall_to_fold_on_empty_list) :-
    select_findall_to_fold_programs(Value, select(Value, [], _),
                                    Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_select_findall_with_ungrounded_template) :-
    select_findall_to_fold_programs(Template, select(Value, [a, b], Rest),
                                    Original, Program),
    assertion(Program =@= Original),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_ground_select_findall_to_fold_with_changed_values) :-
    List = [a, b, a],
    Template = pair(Value, Rest),
    Generator = select(Value, List, Rest),
    select_findall_to_fold_programs(Template, Generator, Original, Program0),
    Program0 = mnn_program(Name, Meta, [Predicate, Helper], ProofData, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                          [mnn_clause(1, numbers(Results),
                                      mnn_loop2_1(_, Results), Source)],
                          Status),
    Program = mnn_program(
                  Name, Meta,
                  [mnn_pred(numbers/1, Modes, Domains,
                            [mnn_clause(1, numbers(Results),
                                        mnn_loop2_1([pair(a, [b, a])], Results),
                                        Source)],
                            Status),
                   Helper],
                  ProofData, Trace),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_nth0_index_findall_to_fold_with_changed_indices) :-
    nth0_findall_to_fold_programs([a, b, a], Original, Program0),
    Program0 = mnn_program(Name, Meta,
                           [Predicate, Helper], Proof, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                         [mnn_clause(1, numbers(Results),
                                     mnn_loop2_1([0, 1, 2], Results),
                                     source(source, 1))],
                         original),
    Program = mnn_program(
                  Name, Meta,
                  [mnn_pred(numbers/1, Modes, Domains,
                            [mnn_clause(1, numbers(Results),
                                        mnn_loop2_1([0, 2], Results),
                                        source(source, 1))],
                            original),
                   Helper],
                  Proof, Trace),
    findall_to_fold_proof(ProofTerm),
    mnn_proof_checker:check_proof(
        Program, Original, ProofTerm, rejected(invalid_or_unsupported_proof)).

test(reject_nth1_index_findall_to_fold_with_changed_indices) :-
    nth1_findall_to_fold_programs([a, b, a], Original, Program0),
    Program0 = mnn_program(Name, Meta, [Predicate, Helper], Proof, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                         [mnn_clause(1, numbers(Results),
                                     mnn_loop2_1([1, 2, 3], Results),
                                     source(source, 1))],
                         original),
    Program = mnn_program(
                  Name, Meta,
                  [mnn_pred(numbers/1, Modes, Domains,
                            [mnn_clause(1, numbers(Results),
                                        mnn_loop2_1([1, 3], Results),
                                        source(source, 1))],
                            original),
                   Helper],
                  Proof, Trace),
    findall_to_fold_proof(ProofTerm),
    mnn_proof_checker:check_proof(
        Program, Original, ProofTerm, rejected(invalid_or_unsupported_proof)).

test(reject_nth0_index_findall_to_fold_with_shared_index_and_element) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Index,
                                                 nth0(Index, [a, 1, c], Index),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_findall_to_fold_with_changed_values) :-
    findall_to_fold_programs(Original, Program0),
    Program0 = mnn_program(Name, Meta, [Predicate, Helper], Proof, Trace),
    Predicate = mnn_pred(numbers/1, Modes, Domains,
                         [mnn_clause(1, numbers(Results),
                                     mnn_loop2_1([a, b], Results),
                                     source(source, 1))],
                         original),
    Program = mnn_program(Name, Meta,
                          [mnn_pred(numbers/1, Modes, Domains,
                                    [mnn_clause(1, numbers(Results),
                                                mnn_loop2_1([a], Results),
                                                source(source, 1))],
                                    original),
                           Helper],
                          Proof, Trace),
    findall_to_fold_proof(ProofTerm),
    mnn_proof_checker:check_proof(
        Program, Original, ProofTerm,
        rejected(invalid_or_unsupported_proof)).

test(accept_ground_member_findall_to_fold_with_arithmetic_filter) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Value,
                                                 conj(member(Value,
                                                             [1, 2, 3, 2]),
                                                      Value > 1),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program0, _),
    Program0 = mnn_program(_, _,
                           [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _),
                                                _)],
                                    _)|_],
                           _, _),
    assertion(Values == [2, 3, 2]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program0, Original, Proof, accepted),
    replace_loop_values(Program0, [2, 2, 3], Program),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_findall_to_fold_with_unsupported_member_filter) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Value,
                                                 conj(member(Value, [a, b]),
                                                      Value \= b),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, loop2_report([])),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_ground_nth0_findall_to_fold_with_arithmetic_filter) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Index,
                                                 conj(nth0(Index,
                                                           [1, 2, 3],
                                                           Value),
                                                      Value > 1),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program0, _),
    Program0 = mnn_program(_, _,
                           [mnn_pred(_, _, _,
                                     [mnn_clause(_, _, mnn_loop2_1(Values, _),
                                                 _)],
                                     _)|_],
                           _, _),
    assertion(Values == [1, 2]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program0, Original, Proof, accepted),
    replace_loop_values(Program0, [2, 1], Program),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_ground_nth1_findall_to_fold_with_arithmetic_filter) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Index,
                                                 conj(nth1(Index,
                                                           [1, 2, 3],
                                                           Value),
                                                      Index > 1),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _),
    Program = mnn_program(_, _,
                          [mnn_pred(_, _, _,
                                    [mnn_clause(_, _, mnn_loop2_1(Values, _),
                                                _)],
                                    _)|_],
                          _, _),
    assertion(Values == [2, 3]),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_findall_to_fold_with_unsupported_nth_filter) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Index,
                                                 conj(nth0(Index,
                                                           [1, 2, 3],
                                                           Value),
                                                      Value \= 2),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, loop2_report([])),
    findall_to_fold_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_findall_to_fold_in_proof_sequence) :-
    findall_to_fold_programs(Original, Program),
    Proof = proof([
        proof_step(1, findall_to_fold, [],
                   equivalent(domain(any), modes([]))),
        proof_step(2, identity, [],
                   equivalent(domain(any), modes([])))
    ]),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_impure_definition_introduction) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(sample/1, ['?'], [any],
                             [mnn_clause(1, sample(X), conj(write(3), check(X)),
                                         source(file, 1))],
                             original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(sample/1, ['?'], [any],
                            [mnn_clause(1, sample(Y),
                                        conj(mnn_definition_1, check(Y)),
                                        source(file, 1))],
                            original),
                   mnn_pred(mnn_definition_1/0, [], [],
                            [mnn_clause(2, mnn_definition_1, write(3),
                                        source(generated, 0))],
                            introduced)],
                  proof([]), trace([])),
    definition_introduction_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_sequence_of_checked_rewrites) :-
    sequence_program(conj(positive(3), true),
                     conj(integer(3), atom(ok)), Original),
    sequence_program(conj(conj(atom(ok), integer(3)), true),
                     conj(atom(ok), integer(3)), Program),
    Proof = proof([
        proof_step(1, reorder_goals, [],
                   equivalent(domain(any), modes([]))),
        proof_step(2, unfold, [],
                   equivalent(domain(any), modes([])))
    ]),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_sequence_with_invalid_intermediate_rewrite) :-
    sequence_program(conj(positive(3), true),
                     conj(integer(3), atom(ok)), Original),
    sequence_program(conj(positive(3), true),
                     conj(atom(ok), integer(3)), Program),
    Proof = proof([
        proof_step(1, reorder_goals, [],
                   equivalent(domain(any), modes([]))),
        proof_step(2, unfold, [],
                   equivalent(domain(any), modes([])))
    ]),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(accept_unfold_with_variable_definition) :-
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
        Program, Original, Proof, accepted).

test(accept_fold_with_variable_definition) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                           [mnn_clause(1, positive(X), integer(X),
                                       source(file, 1))],
                           original),
                  mnn_pred(result/1, ['?'], [any],
                           [mnn_clause(2, result(Y), integer(Y),
                                       source(file, 2))],
                           original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                          [mnn_clause(1, positive(A), integer(A),
                                      source(file, 1))],
                          original),
                   mnn_pred(result/1, ['?'], [any],
                          [mnn_clause(2, result(B), positive(B),
                                      source(file, 2))],
                          original)],
                  proof([]), trace([])),
    definition_rewrite_proof(fold, Proof),
    mnn_proof_checker:check_proof(Program, Original, Proof, accepted).

test(reject_fold_when_variable_sharing_differs) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                           [mnn_clause(1, positive(X),
                                       conj(integer(X), number(X)),
                                       source(file, 1))],
                           original),
                  mnn_pred(result/2, ['?', '?'], [any, any],
                           [mnn_clause(2, result(A, B),
                                       conj(integer(A), number(B)),
                                       source(file, 2))],
                           original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                          [mnn_clause(1, positive(Y),
                                      conj(integer(Y), number(Y)),
                                      source(file, 1))],
                          original),
                   mnn_pred(result/2, ['?', '?'], [any, any],
                          [mnn_clause(2, result(C, D), positive(C),
                                      source(file, 2))],
                          original)],
                  proof([]), trace([])),
    definition_rewrite_proof(fold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_unfold_with_impure_variable_definition) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                           [mnn_clause(1, positive(X), write(X),
                                       source(file, 1))],
                           original),
                  mnn_pred(result/1, ['?'], [any],
                           [mnn_clause(2, result(Y), positive(Y),
                                       source(file, 2))],
                           original)],
                   proof([]), trace([])),
    Program = mnn_program(
                  sample, meta(file, []),
                  [mnn_pred(positive/1, ['?'], [any],
                          [mnn_clause(1, positive(A), write(A),
                                      source(file, 1))],
                          original),
                   mnn_pred(result/1, ['?'], [any],
                          [mnn_clause(2, result(B), write(B),
                                      source(file, 2))],
                          original)],
                  proof([]), trace([])),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_unfold_with_unbound_definition_body) :-
    Original = mnn_program(
                   sample, meta(file, []),
                   [mnn_pred(positive/1, ['?'], [any],
                             [mnn_clause(1, positive(X), Body,
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
                            [mnn_clause(1, positive(Y), ProgramBody,
                                        source(file, 1))],
                            original),
                   mnn_pred(result/0, [], [],
                            [mnn_clause(2, result, integer(3),
                                        source(file, 2))],
                            original)],
                  proof([]), trace([])),
    definition_rewrite_proof(unfold, Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)),
    assertion(var(Body)),
    assertion(var(ProgramBody)).

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

test(reject_multiple_reorderings_in_one_step) :-
    multiple_reordering_programs(Original, Program),
    reorder_proof(Proof),
    mnn_proof_checker:check_proof(
        Program, Original, Proof, rejected(invalid_or_unsupported_proof)).

test(reject_multiple_reorderings_in_proof_sequence) :-
    multiple_reordering_programs(Original, Program),
    Proof = proof([
        proof_step(1, identity, [],
                   equivalent(domain(any), modes([]))),
        proof_step(2, reorder_goals, [],
                   equivalent(domain(any), modes([])))
    ]),
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
    assertion(sub_string(Markdown, _, _, _, 'pure type tests')).

test(render_checked_definition_introduction) :-
    definition_introduction_program(Original, Program),
    definition_introduction_proof(Proof),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, 'introduce_definition')),
    assertion(sub_string(Markdown, _, _, _, 'helper predicate')).

test(render_checked_findall_to_fold) :-
    findall_to_fold_programs(Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, 'findall_to_fold')),
    assertion(sub_string(Markdown, _, _, _, 'ground proper-list')),
    assertion(sub_string(Markdown, _, _, _, 'Independent check:** accepted.')).

test(render_checked_nth0_index_findall_to_fold) :-
    nth0_findall_to_fold_programs([a, b], Original, Program),
    findall_to_fold_proof(Proof),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, 'findall_to_fold')),
    assertion(sub_string(Markdown, _, _, _, '**Independent check:** accepted.')).

test(render_checked_rewrite_sequence) :-
    sequence_program(conj(positive(3), true),
                     conj(integer(3), atom(ok)), Original),
    sequence_program(conj(conj(atom(ok), integer(3)), true),
                     conj(atom(ok), integer(3)), Program),
    Proof = proof([
        proof_step(1, reorder_goals, [],
                   equivalent(domain(any), modes([]))),
        proof_step(2, unfold, [],
                   equivalent(domain(any), modes([])))
    ]),
    mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown),
    assertion(sub_string(Markdown, _, _, _, '## Step 1: `reorder_goals`')),
    assertion(sub_string(Markdown, _, _, _, '## Step 2: `unfold`')),
    assertion(sub_string(Markdown, _, _, _, '**Independent check:** accepted.')).

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

definition_introduction_proof(
    proof([proof_step(1, introduce_definition, [],
                      equivalent(domain(any), modes([])))])).

definition_introduction_program(
    mnn_program(sample, meta(file, []),
                [mnn_pred(sample/1, ['?'], [any],
                          [mnn_clause(1, sample(X),
                                      conj(integer(3), check(X)),
                                      source(file, 1))],
                          original)],
                proof([]), trace([])),
    mnn_program(sample, meta(file, []),
                [mnn_pred(sample/1, ['?'], [any],
                          [mnn_clause(1, sample(Y),
                                      conj(mnn_definition_1, check(Y)),
                                      source(file, 1))],
                          original),
                 mnn_pred(mnn_definition_1/0, [], [],
                          [mnn_clause(2, mnn_definition_1, integer(3),
                                      source(generated, 0))],
                          introduced)],
                proof([]), trace([]))).

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

sequence_program(CallerBody, DefinitionBody,
                 mnn_program(sample, meta(file, []),
                             [mnn_pred(result/0, [], [],
                                       [mnn_clause(
                                           2, result, CallerBody,
                                           source(file, 2))],
                                       original),
                              mnn_pred(positive/1, ['?'], [any],
                                       [mnn_clause(
                                           1, positive(3), DefinitionBody,
                                           source(file, 1))],
                                       original)],
                             proof([]), trace([]))).

program_with_body(Body,
                  mnn_program(sample, meta(file, []),
                              [mnn_pred(sample/1, ['?'], [any],
                                        [mnn_clause(1, sample(_), Body,
                                                    source(file, 1))],
                                        original)],
                              proof([]), trace([]))).

multiple_reordering_programs(
    mnn_program(sample, meta(file, []),
                [mnn_pred(first/1, ['?'], [any],
                          [mnn_clause(1, first(_), conj(integer(3), atom(ok)),
                                      source(file, 1))],
                          original),
                 mnn_pred(second/1, ['?'], [any],
                          [mnn_clause(2, second(_), conj(number(4), ground(foo)),
                                      source(file, 2))],
                          original)],
                proof([]), trace([])),
    mnn_program(sample, meta(file, []),
                [mnn_pred(first/1, ['?'], [any],
                          [mnn_clause(1, first(_), conj(atom(ok), integer(3)),
                                      source(file, 1))],
                          original),
                 mnn_pred(second/1, ['?'], [any],
                          [mnn_clause(2, second(_), conj(ground(foo), number(4)),
                                      source(file, 2))],
                          original)],
                proof([]), trace([]))).

findall_to_fold_programs(
    Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                   [mnn_clause(1, numbers(Results),
                               findall(Value,
                                       member(Value, [a, b]),
                                       Results),
                               source(source, 1))],
                   original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

fact_findall_to_fold_programs(
    Template, Generator, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1), clause(2), clause(3),
                                         clause(4)]),
                   [mnn_pred(pair/2, ['?', '?'], [any, any],
                             [mnn_clause(1, pair(a, 1), true, source(source, 1)),
                              mnn_clause(2, pair(b, 2), true, source(source, 2)),
                              mnn_clause(3, pair(a, 1), true, source(source, 3))],
                             original),
                    mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(4, numbers(Results),
                                         findall(Template, Generator, Results),
                                         source(source, 4))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

rule_findall_to_fold_programs(Original, Program) :-
                   Original = mnn_program(
                                  sample,
                                  meta(source, [clause(1), clause(2), clause(3), clause(4),
                                                clause(5), clause(6)]),
                                  [mnn_pred(num/1, ['?'], [integer],
                                            [mnn_clause(1, num(1), true, source(source, 1)),
                                             mnn_clause(2, num(2), true, source(source, 2)),
                                             mnn_clause(3, num(3), true, source(source, 3))],
                                            original),
                                   mnn_pred(positive/1, ['?'], [integer],
                                            [mnn_clause(4, positive(Value),
                                                        conj(disj(num(Value), num(Value)),
                                                             Value > 1),
                                                        source(source, 4)),
                                             mnn_clause(5, positive(0), true,
                                                        source(source, 5))],
                                            original),
                                   mnn_pred(numbers/1, ['?'], [list(integer)],
                                            [mnn_clause(6, numbers(Results),
                                                        findall(Value,
                                                                conj(positive(Value),
                                                                     Value =< 2),
                                                                Results),
                                                        source(source, 6))],
                                            original)],
                                  proof([]), trace([])),
                   mnn_loop2:convert_program(Original, Program, _).

nth0_findall_to_fold_programs(
    List, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Index,
                                                 nth0(Index, List, _),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

nth1_findall_to_fold_programs(
    List, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Index,
                                                 nth1(Index, List, _),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

length_findall_to_fold_programs(
    Length, List, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                         findall(Length,
                                                 length(List, Length),
                                                 Results),
                                         source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

filtered_length_findall_to_fold_programs(
    Template, Length, List, Filter, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(
                                  1, numbers(Results),
                                  findall(Template,
                                          conj(length(List, Length), Filter),
                                          Results),
                                  source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

between_findall_to_fold_programs(
    Low, High, Value, Template, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(
                                  1, numbers(Results),
                                  findall(Template, between(Low, High, Value),
                                          Results),
                                  source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

filtered_between_findall_to_fold_programs(Value, Filter, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                            [mnn_clause(
                                 1, numbers(Results),
                                 findall(Value,
                                         conj(between(1, 5, Value), Filter),
                                         Results),
                                 source(source, 1))],
                            original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

select_findall_to_fold_programs(
    Template, Generator, Original, Program) :-
    Original = mnn_program(
                   sample, meta(source, [clause(1)]),
                   [mnn_pred(numbers/1, ['?'], [any],
                             [mnn_clause(1, numbers(Results),
                                        findall(Template, Generator, Results),
                                        source(source, 1))],
                             original)],
                   proof([]), trace([])),
    mnn_loop2:convert_program(Original, Program, _).

findall_to_fold_proof(
    proof([proof_step(1, findall_to_fold, [],
                      equivalent(domain(any), modes([])))])).

replace_loop_values(
    mnn_program(Name, Meta,
                [mnn_pred(Key, Modes, Domains,
                          [mnn_clause(Id, Head, LoopCall, Location)],
                          Status)|Predicates],
                Proof, Trace),
    Values,
    mnn_program(Name, Meta,
                [mnn_pred(Key, Modes, Domains,
                          [mnn_clause(Id, Head, ChangedLoopCall, Location)],
                          Status)|Predicates],
                Proof, Trace)) :-
    LoopCall =.. [Loop, _, Results],
    ChangedLoopCall =.. [Loop, Values, Results].

:- end_tests(mnn_proof_checker).

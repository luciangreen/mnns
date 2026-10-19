:- begin_tests(mnn_algebraplop).

:- use_module('../prolog/algebraplop/algebraplop').

test(infers_constant_sequence) :-
    mnn_algebraplop:infer_sequence_formula(
        [7, 7, 7, 7], formula(constant(7), verified_on([7, 7, 7, 7]))).

test(infers_exact_linear_sequence_with_zero_based_positions) :-
    mnn_algebraplop:infer_sequence_formula(
        [3, 5, 7, 9], formula(linear(2, 3), verified_on([3, 5, 7, 9]))).

test(infers_exact_quadratic_sequence_with_zero_based_positions) :-
    mnn_algebraplop:infer_sequence_formula(
        [1, 4, 9, 16],
        formula(quadratic(1, 3, 2), verified_on([1, 4, 9, 16]))).

test(infers_cubic_sequence_with_held_out_sample) :-
    mnn_algebraplop:infer_sequence_formula(
        [1, 8, 27, 64, 125],
        formula(polynomial([1, 7, 12, 6]),
                verified_on([1, 8, 27, 64, 125]))).

test(infers_quartic_sequence_with_multiple_held_out_samples) :-
    mnn_algebraplop:infer_sequence_formula(
        [0, 1, 16, 81, 256, 625],
        formula(polynomial([0, 1, 14, 36, 24]),
                verified_on([0, 1, 16, 81, 256, 625]))).

test(infers_geometric_sequence_with_held_out_samples) :-
    mnn_algebraplop:infer_sequence_formula(
        [2, 4, 8, 16],
        formula(exponential(2, 2), verified_on([2, 4, 8, 16]))).

test(infers_geometric_sequence_with_negative_base) :-
    mnn_algebraplop:infer_sequence_formula(
        [-2, 4, -8, 16],
        formula(exponential(-2, -2), verified_on([-2, 4, -8, 16]))).

test(infers_geometric_sequence_with_zero_base) :-
    mnn_algebraplop:infer_sequence_formula(
        [5, 0, 0], formula(exponential(5, 0), verified_on([5, 0, 0]))).

test(rejects_geometric_candidate_that_fails_held_out_sample) :-
    mnn_algebraplop:infer_sequence_formula([2, 4, 8, 15], no_formula).

test(rejects_higher_degree_candidate_that_fails_held_out_sample) :-
    mnn_algebraplop:infer_sequence_formula([0, 1, 8, 27, 80], no_formula).

test(rejects_quadratic_fit_without_held_out_sample) :-
    mnn_algebraplop:infer_sequence_formula([1, 4, 9], no_formula).

test(rejects_inconsistent_quadratic_sequence) :-
    mnn_algebraplop:infer_sequence_formula([1, 4, 9, 16, 15], no_formula).

test(rejects_quadratic_candidate_that_fails_held_out_sample) :-
    mnn_algebraplop:infer_sequence_formula([1, 4, 9, 15], no_formula).

test(rejects_prime_sequence) :-
    mnn_algebraplop:infer_sequence_formula([2, 3, 5, 7, 11], no_formula).

test(requires_held_out_samples) :-
    mnn_algebraplop:infer_sequence_formula([3, 5], no_formula).

test(rejects_non_integer_or_improper_samples) :-
    mnn_algebraplop:infer_sequence_formula([1, 2.5, 4], no_formula),
    mnn_algebraplop:infer_sequence_formula([1, 2|tail], no_formula).

test(inference_is_deterministic) :-
    call_cleanup(
        mnn_algebraplop:infer_sequence_formula([1, 4, 9, 16], _),
        Deterministic = true),
    assertion(Deterministic == true).

test(inverts_affine_sequence_at_nonnegative_position) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(2, 3), verified_on([3, 5, 7, 9])),
        9, position(3)).

test(inverts_affine_sequence_with_negative_slope) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(-2, 7), verified_on([7, 5, 3, 1])),
        3, position(2)).

test(rejects_value_not_on_affine_sequence) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(2, 3), verified_on([3, 5, 7, 9])),
        8, no_position).

test(rejects_affine_solution_at_negative_position) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(2, 3), verified_on([3, 5, 7, 9])),
        1, no_position).

test(inverts_constant_formula_to_all_positions) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(constant(4), verified_on([4, 4, 4])),
        4, all_positions).

test(rejects_value_not_matching_constant_formula) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(constant(4), verified_on([4, 4, 4])),
        5, no_position).

test(handles_zero_slope_affine_formula) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(0, 4), verified_on([4, 4, 4])),
        4, all_positions),
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(0, 4), verified_on([4, 4, 4])),
        5, no_position).

test(rejects_unsupported_or_invalid_inverse_inputs) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([1, 2, 1]), verified_on([1, 3, 6])),
        8, no_position),
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(2, 3), verified_on([3, 5, 7])),
        8.0, no_position),
    mnn_algebraplop:invert_sequence_formula(
        formula(linear(slope, 3), verified_on([3, 5, 7])),
        7, no_position).

test(inverts_polynomial_at_unique_nonnegative_position) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([1, 1, 2]), verified_on([1, 2, 5])),
        17, position(4)).

test(inverts_polynomial_at_multiple_positions) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([0, 3, -6, 6]), verified_on([0, 3, 0, -3])),
        0, positions([0, 2, 4])).

test(rejects_value_absent_from_polynomial) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([1, 1, 2]), verified_on([1, 2, 5])),
        0, no_position).

test(inverts_constant_polynomial_at_all_positions) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([4, 0, 0]), verified_on([4, 4, 4])),
        4, all_positions),
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([4, 0, 0]), verified_on([4, 4, 4])),
        5, no_position).

test(trims_zero_leading_newton_coefficients) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([1, 2, 0, 0]), verified_on([1, 3, 5])),
        7, position(3)).

test(rejects_invalid_polynomial_inverse_inputs) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([]), verified_on([])), 1, no_position),
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([1, coefficient]), verified_on([])), 1, no_position),
    mnn_algebraplop:invert_sequence_formula(
        formula(polynomial([1, 2]), verified_on([])), 3.0, no_position).

test(inverts_geometric_sequence) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(2, 3), verified_on([2, 6, 18, 54])),
        54, position(3)).

test(inverts_geometric_sequence_with_negative_base) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(-2, -2), verified_on([-2, 4, -8, 16])),
        -8, position(2)).

test(inverts_geometric_sequence_with_negative_initial_value) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(-3, 2), verified_on([-3, -6, -12])),
        -12, position(2)).

test(rejects_value_not_on_geometric_sequence) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(2, 3), verified_on([2, 6, 18, 54])),
        36, no_position).

test(inverts_constant_geometric_sequences) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(5, 1), verified_on([5, 5, 5])),
        5, all_positions),
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(5, 1), verified_on([5, 5, 5])),
        4, no_position),
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(0, 2), verified_on([0, 0, 0])),
        0, all_positions).

test(inverts_alternating_geometric_sequences) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(3, -1), verified_on([3, -3, 3, -3])),
        3, positions(0, 2)),
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(3, -1), verified_on([3, -3, 3, -3])),
        -3, positions(1, 2)),
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(3, -1), verified_on([3, -3, 3, -3])),
        2, no_position).

test(inverts_zero_base_geometric_sequence) :-
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(5, 0), verified_on([5, 0, 0])),
        5, position(0)),
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(5, 0), verified_on([5, 0, 0])),
        0, positions(1, 1)),
    mnn_algebraplop:invert_sequence_formula(
        formula(exponential(5, 0), verified_on([5, 0, 0])),
        1, no_position).

test(geometric_inverse_is_deterministic) :-
    call_cleanup(
        mnn_algebraplop:invert_sequence_formula(
            formula(exponential(-2, -2), verified_on([-2, 4, -8])), -8, _),
        Deterministic = true),
    assertion(Deterministic == true).

test(inverse_is_deterministic) :-
    call_cleanup(
        mnn_algebraplop:invert_sequence_formula(
            formula(linear(2, 3), verified_on([3, 5, 7, 9])), 9, _),
        Deterministic = true),
    assertion(Deterministic == true).

:- end_tests(mnn_algebraplop).

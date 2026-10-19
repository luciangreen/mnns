:- begin_tests(mnn_algebraplop).

:- use_module('../prolog/algebraplop/algebraplop').

test(infers_constant_sequence) :-
    mnn_algebraplop:infer_sequence_formula(
        [7, 7, 7, 7], formula(constant(7), verified_on([7, 7, 7, 7]))).

test(infers_exact_linear_sequence_with_zero_based_positions) :-
    mnn_algebraplop:infer_sequence_formula(
        [3, 5, 7, 9], formula(linear(2, 3), verified_on([3, 5, 7, 9]))).

test(rejects_exponential_sequence_as_linear) :-
    mnn_algebraplop:infer_sequence_formula([2, 4, 8, 16], no_formula).

test(rejects_prime_sequence) :-
    mnn_algebraplop:infer_sequence_formula([2, 3, 5, 7, 11], no_formula).

test(requires_held_out_samples) :-
    mnn_algebraplop:infer_sequence_formula([3, 5], no_formula).

test(rejects_non_integer_or_improper_samples) :-
    mnn_algebraplop:infer_sequence_formula([1, 2.5, 4], no_formula),
    mnn_algebraplop:infer_sequence_formula([1, 2|tail], no_formula).

test(inference_is_deterministic) :-
    call_cleanup(
        mnn_algebraplop:infer_sequence_formula([3, 5, 7, 9], _),
        Deterministic = true),
    assertion(Deterministic == true).

:- end_tests(mnn_algebraplop).

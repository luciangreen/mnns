:- module(mnn_proof_checker,
          [ check_proof/4
          ]).

check_proof(Program, Original, Proof, Result) :-
    (   mnn_program_term(Program),
        mnn_program_term(Original)
    ->  check_identity_proof(Program, Original, Proof, Result)
    ;   Result = rejected(invalid_program)
    ).

mnn_program_term(Program) :-
    nonvar(Program),
    functor(Program, mnn_program, 5).

check_identity_proof(Program, Original, Proof, Result) :-
    (   valid_identity_proof(Proof)
    ->  (   Program =@= Original
        ->  Result = accepted
        ;   Result = rejected(programs_differ)
        )
    ;   Result = rejected(invalid_or_unsupported_proof)
    ).

valid_identity_proof(Proof) :-
    ground(Proof),
    Proof = proof([Step]),
    Step = proof_step(Id, Rule, Premises, Conclusion),
    integer(Id),
    Id > 0,
    Rule == identity,
    Premises == [],
    Conclusion = equivalent(domain(Domain), modes(Modes)),
    ground(Domain),
    ground(Modes).

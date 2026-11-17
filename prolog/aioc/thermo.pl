:- module(mnn_aioc_thermo,
          [ incorporate_thermo/5,
            thermo_incorporation_proof/3
          ]).

/** <module> AIOC incorporation of a thermo type class

incorporate_thermo(Name, Alphabet, Counts, Program, Proof) turns the type
class with those counts into an MNN program of facts Name(Rank, Sequence),
one per rank, and proves it. The proof has two steps, and
mnn_proof_checker:check_proof/4 checks both before the program is returned:

  1. incorporate_thermo: the program is exactly the table the coder gives
     for this class (the checker builds it again and compares),
  2. thermo_induction: the coder is a bijection from every class onto its
     ranks, for every length (checked by mnn_thermo_induction).

So the facts are the class, each sequence once, in rank order, and the
program runs in both directions.
*/

:- use_module(library(error)).
:- use_module('../proof/proof_checker').
:- use_module('../thermo/thermo', []).
:- use_module('../thermo/thermo_induction', []).

incorporate_thermo(Name, Alphabet, Counts, Program, Proof) :-
    must_be(atom, Name),
    Source = thermo_source(Name, Alphabet, Counts),
    (   mnn_thermo:thermo_table_program(Name, Alphabet, Counts, Program)
    ->  thermo_incorporation_proof(Alphabet, Counts, Proof),
        mnn_proof_checker:check_proof(Program, Source, Proof, accepted)
    ;   throw(error(domain_error(thermo_source, Source), _))
    ).

thermo_incorporation_proof(Alphabet, Counts,
    proof([proof_step(1, incorporate_thermo, [],
                      equivalent(domain(type_class(Alphabet, Counts)),
                                 modes(all))),
           proof_step(2, thermo_induction, [], Induction)])) :-
    mnn_thermo_induction:thermo_induction_proof(Induction).

:- module(mnn_proof_renderer,
          [ render_proof/4
          ]).

:- use_module(proof_checker).

render_proof(Program, Original, Proof, Markdown) :-
    mnn_proof_checker:check_proof(Program, Original, Proof, Result),
    with_output_to(string(Markdown),
                   render_report(Result, Proof)).

render_report(accepted, proof([proof_step(Id, identity, [],
                                           equivalent(domain(Domain),
                                                      modes(Modes)))])) :-
    !,
    format('# Proof report~n~n', []),
    format('**Independent check:** accepted.~n~n', []),
    format('## Step ~d: `identity`~n~n', [Id]),
    format('The complete MNN IR terms are alpha-equivalent. ', []),
    format('No program rewrite is claimed.~n~n', []),
    format('- Domain: `~q`~n', [Domain]),
    format('- Modes: `~q`~n', [Modes]).
render_report(Result, Proof) :-
    format('# Proof report~n~n', []),
    format('**Independent check:** `~q`.~n~n', [Result]),
    format('## Machine proof~n~n```prolog~n', []),
    write_term(Proof, [quoted(true), numbervars(true)]),
    format('~n```~n', []).

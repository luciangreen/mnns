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
render_report(accepted, proof([proof_step(Id, reorder_goals, [],
                                          equivalent(domain(Domain),
                                                    modes(Modes)))])) :-
    !,
    format('# Proof report~n~n', []),
    format('**Independent check:** accepted.~n~n', []),
    format('## Step ~d: `reorder_goals`~n~n', [Id]),
    format('One adjacent pair of ground calls to pure unary type tests ', []),
    format('was swapped in a clause body. The checker does not infer domain ', []),
    format('or mode annotations, and certifies no other changes.~n~n', []),
    format('- Domain: `~q`~n', [Domain]),
    format('- Modes: `~q`~n', [Modes]).
render_report(accepted, proof([proof_step(Id, Rule, [],
                                          equivalent(domain(Domain),
                                                     modes(Modes)))])) :-
    memberchk(Rule, [unfold, fold]),
    !,
    format('# Proof report~n~n', []),
    format('**Independent check:** accepted.~n~n', []),
    format('## Step ~d: `~w`~n~n', [Id, Rule]),
    render_definition_rewrite(Rule),
    format('- Domain: `~q`~n', [Domain]),
    format('- Modes: `~q`~n', [Modes]).
render_report(Result, Proof) :-
    format('# Proof report~n~n', []),
    format('**Independent check:** `~q`.~n~n', [Result]),
    format('## Machine proof~n~n```prolog~n', []),
    write_term(Proof, [quoted(true), numbervars(true)]),
    format('~n```~n', []).

render_definition_rewrite(unfold) :-
    format('One ground call was expanded using its matching single-clause ', []),
    format('definition with a ground body made only of pure built-ins.~n~n', []).
render_definition_rewrite(fold) :-
    format('One ground body was replaced by its matching single-clause call; ', []),
    format('the definition body uses only pure built-ins.~n~n', []).

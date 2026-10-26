:- module(mnn_aioc_dtree,
          [ incorporate_dtree/5
          ]).

:- use_module(library(error)).
:- use_module('../proof/proof_checker').

incorporate_dtree(Name, Input, Tree, Program, Proof) :-
    must_be(atom, Name),
    (   var(Input)
    ->  true
    ;   throw(error(type_error(variable, Input), _))
    ),
    Source = dtree_source(Name, Input, Tree),
    (   valid_dtree_source(Source)
    ->  build_dtree_program(Name, Input, Tree, Program),
        dtree_incorporation_proof(Proof),
        mnn_proof_checker:check_proof(Program, Source, Proof, accepted)
    ;   throw(error(domain_error(dtree_source, Source), _))
    ).

valid_dtree_source(dtree_source(Name, Input, Tree)) :-
    atom(Name),
    var(Input),
    acyclic_term(Tree),
    valid_dtree(Tree, Input).

valid_dtree(leaf(Value), Input) :-
    !,
    variables_are_input(Value, Input).
valid_dtree(dtree(Test, Yes, No), Input) :-
    valid_dtree_test(Test, Input),
    valid_dtree(Yes, Input),
    valid_dtree(No, Input).

valid_dtree_test(Test, Input) :-
    nonvar(Test),
    callable(Test),
    term_variables(Test, Variables),
    maplist(variable_is_input(Input), Variables),
    functor(Test, Name, Arity),
    valid_test_shape(Name, Arity, Test, Input).

valid_test_shape(Name, 1, Test, _) :-
    memberchk(Name, [atom, atomic, compound, ground, integer, is_list, number]),
    arg(1, Test, _).
valid_test_shape(Name, 2, Test, Input) :-
    memberchk(Name, ['<', '=<', '>', '>=', '=:=', '=\\=']),
    arg(1, Test, Left),
    arg(2, Test, Right),
    valid_tree_expression(Left, Input),
    valid_tree_expression(Right, Input).

valid_tree_expression(Expression, Input) :-
    var(Expression),
    !,
    Expression == Input.
valid_tree_expression(Expression, _) :-
    number(Expression),
    !.
valid_tree_expression(Expression, Input) :-
    compound(Expression),
    functor(Expression, Name, Arity),
    valid_expression_operator(Name, Arity),
    Expression =.. [_|Arguments],
    maplist(valid_tree_expression_with_input(Input), Arguments).

valid_tree_expression_with_input(Input, Expression) :-
    valid_tree_expression(Expression, Input).

valid_expression_operator('+', 1).
valid_expression_operator('-', 1).
valid_expression_operator('+', 2).
valid_expression_operator('-', 2).
valid_expression_operator('*', 2).
valid_expression_operator('/', 2).
valid_expression_operator('//', 2).
valid_expression_operator(mod, 2).
valid_expression_operator(rem, 2).
valid_expression_operator(abs, 1).
valid_expression_operator(max, 2).
valid_expression_operator(min, 2).
valid_expression_operator('**', 2).
valid_expression_operator('^', 2).

variables_are_input(Term, Input) :-
    term_variables(Term, Variables),
    maplist(variable_is_input(Input), Variables).

variable_is_input(Input, Variable) :-
    Variable == Input.

build_dtree_program(Name, Input, Tree, Program) :-
    Output = _,
    dtree_body(Tree, Output, Body),
    Head =.. [Name, Input, Output],
    Predicate = mnn_pred(
                    Name/2, ['?', '?'], [any, any],
                    [mnn_clause(1, Head, Body,
                                source(dtree(Name), 1))],
                    original),
    Program = mnn_program(
                  Name, meta(dtree(Name), [clause(1)]),
                  [Predicate], proof([]), trace([])).

dtree_body(leaf(Value), Output, Output = Value).
dtree_body(dtree(Test, Yes, No), Output, ite(Test, YesBody, NoBody)) :-
    dtree_body(Yes, Output, YesBody),
    dtree_body(No, Output, NoBody).

dtree_incorporation_proof(
    proof([proof_step(1, incorporate_dtree, [],
                      equivalent(domain(all), modes(all)))])).

:- module(mnn_starlog,
          [ starlog_to_ir/2,
            starlog_to_ir/3,
            ir_to_starlog/2,
            coerce_text/2,
            coerce_atom/2,
            op(500, yfx, '&'),
            op(500, yfx, '•')
          ]).

:- use_module(library(lists)).

:- op(500, yfx, '&').
:- op(500, yfx, '•').

starlog_to_ir(Program, IRProgram) :-
    starlog_to_ir(Program, [], IRProgram).

starlog_to_ir(Program, Options, IRProgram) :-
    (   valid_options(Options)
    ->  true
    ;   throw(error(domain_error(starlog_options, Options), _))
    ),
    Program = mnn_program(Name, meta(Source, Events), Predicates, Proof, Trace),
    function_declarations(Events, Functions),
    transform_predicates(Predicates, Functions, Options,
                         TransformedPredicates),
    IRProgram = mnn_program(Name, meta(Source, Events),
                            TransformedPredicates, Proof, Trace).

ir_to_starlog(
    mnn_program(Name, meta(Source, Events), Predicates, Proof, Trace),
    StarlogProgram) :-
    function_declarations(Events, Functions),
    reverse_predicates(Predicates, Functions, StarlogPredicates),
    StarlogProgram = mnn_program(Name, meta(Source, Events),
                                 StarlogPredicates, Proof, Trace).

valid_options(Options) :-
    is_list(Options),
    maplist(valid_option, Options),
    findall(Value, member(coerce(Value), Options), Values),
    (   Values = []
    ->  true
    ;   Values = [true]
    ).

valid_option(coerce(true)).
valid_option(coerce(false)).

function_declarations(Events, Functions) :-
    findall(Name/Arity,
            ( member(directive(_, starlog_function(Name/Arity)), Events),
              atom(Name),
              integer(Arity),
              Arity >= 0
            ),
            Declared),
    list_to_set(Declared, Functions).

transform_predicates([], _, _, []).
transform_predicates(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    Functions, Options,
    [mnn_pred(Key, Modes, Domains, TransformedClauses, Status)|Transformed]) :-
    transform_clauses(Clauses, Functions, Options, TransformedClauses),
    transform_predicates(Predicates, Functions, Options, Transformed).

transform_clauses([], _, _, []).
transform_clauses(
    [mnn_clause(Id, Head, Body, Location)|Clauses],
    Functions, Options,
    [mnn_clause(Id, Head, TransformedBody, Location)|Transformed]) :-
    transform_goal(Body, Functions, Options, TransformedBody),
    transform_clauses(Clauses, Functions, Options, Transformed).

transform_goal(conj(Left, Right), Functions, Options,
               conj(NewLeft, NewRight)) :-
    !,
    transform_goal(Left, Functions, Options, NewLeft),
    transform_goal(Right, Functions, Options, NewRight).
transform_goal(disj(Left, Right), Functions, Options,
               disj(NewLeft, NewRight)) :-
    !,
    transform_goal(Left, Functions, Options, NewLeft),
    transform_goal(Right, Functions, Options, NewRight).
transform_goal(ite(If, Then, Else), Functions, Options,
               ite(NewIf, NewThen, NewElse)) :-
    !,
    transform_goal(If, Functions, Options, NewIf),
    transform_goal(Then, Functions, Options, NewThen),
    transform_goal(Else, Functions, Options, NewElse).
transform_goal(not(Goal), Functions, Options, not(NewGoal)) :-
    !,
    transform_goal(Goal, Functions, Options, NewGoal).
transform_goal(once(Goal), Functions, Options, once(NewGoal)) :-
    !,
    transform_goal(Goal, Functions, Options, NewGoal).
transform_goal(is(Output, Expression), Functions, Options, Goal) :-
    !,
    starlog_expression(Expression, Output, Functions, Options, Goals),
    goals_conjunction(Goals, Goal).
transform_goal(Goal, _, _, Goal).

starlog_expression(Expression, Output, _, _, [Module:Predicate]) :-
    module_function(Expression, Module, Call),
    !,
    append_output_argument(Call, Output, Predicate).
starlog_expression(Expression, Output, Functions, Options, Goals) :-
    string_concat_expression(Expression, Left, Right),
    !,
    ensure_text_operand(Left, Options),
    ensure_text_operand(Right, Options),
    compile_argument(Left, Functions, Options, LeftValue, LeftGoals),
    compile_argument(Right, Functions, Options, RightValue, RightGoals),
    text_arguments(LeftValue, RightValue, Options, CoercionGoals,
                   ConcatLeft, ConcatRight),
    append([LeftGoals, RightGoals, CoercionGoals,
            [string_concat(ConcatLeft, ConcatRight, Output)]], Goals).
starlog_expression(Expression, Output, Functions, Options, Goals) :-
    list_concat_expression(Expression, Left, Right),
    !,
    compile_argument(Left, Functions, Options, LeftValue, LeftGoals),
    compile_argument(Right, Functions, Options, RightValue, RightGoals),
    append([LeftGoals, RightGoals, [append(LeftValue, RightValue, Output)]],
           Goals).
starlog_expression(Expression, Output, Functions, Options, Goals) :-
    atom_concat_expression(Expression, Left, Right),
    !,
    ensure_atom_operand(Left, Options),
    ensure_atom_operand(Right, Options),
    compile_argument(Left, Functions, Options, LeftValue, LeftGoals),
    compile_argument(Right, Functions, Options, RightValue, RightGoals),
    atom_arguments(LeftValue, RightValue, Options, CoercionGoals,
                   ConcatLeft, ConcatRight),
    append([LeftGoals, RightGoals, CoercionGoals,
            [atom_concat(ConcatLeft, ConcatRight, Output)]], Goals).
starlog_expression(Expression, Output, Functions, _, [Predicate]) :-
    declared_function_call(Expression, Functions, Call),
    !,
    append_output_argument(Call, Output, Predicate).
starlog_expression(Expression, Output, Functions, Options, Goals) :-
    arithmetic_expression(Expression),
    !,
    compile_arithmetic(Expression, Functions, Options,
                       ArithmeticExpression, PrefixGoals),
    append(PrefixGoals, [is(Output, ArithmeticExpression)], Goals).
starlog_expression(Expression, Output, _, _, [is(Output, Expression)]) :-
    (   var(Expression)
    ;   atomic(Expression)
    ),
    !.
starlog_expression(Expression, _, _, _, _) :-
    callable(Expression),
    !,
    functor(Expression, Name, Arity),
    throw(error(existence_error(starlog_function, Name/Arity), _)).
starlog_expression(Expression, _, _, _, _) :-
    throw(error(domain_error(starlog_expression, Expression), _)).

module_function(Expression, Module, Call) :-
    nonvar(Expression),
    Expression = Module:Call,
    atom(Module),
    compound(Call),
    !.

string_concat_expression(Expression, Left, Right) :-
    nonvar(Expression),
    Expression =.. [':', Left, Right],
    \+ module_function(Expression, _, _).

list_concat_expression(Expression, Left, Right) :-
    nonvar(Expression),
    Expression =.. ['&', Left, Right].

atom_concat_expression(Expression, Left, Right) :-
    nonvar(Expression),
    Expression =.. ['•', Left, Right].

declared_function_call(Expression, Functions, Expression) :-
    compound(Expression),
    functor(Expression, Name, Arity),
    memberchk(Name/Arity, Functions).
declared_function_call(Expression, Functions, Expression) :-
    atom(Expression),
    memberchk(Expression/0, Functions).

append_output_argument(Call, Output, Predicate) :-
    Call =.. [Name|Arguments],
    append(Arguments, [Output], OutputArguments),
    Predicate =.. [Name|OutputArguments].

arithmetic_expression(Expression) :-
    compound(Expression),
    Expression =.. [Functor|Arguments],
    arithmetic_functor(Functor, Arity),
    length(Arguments, Arity).

arithmetic_functor(+, 1).
arithmetic_functor(-, 1).
arithmetic_functor(abs, 1).
arithmetic_functor(sign, 1).
arithmetic_functor(float, 1).
arithmetic_functor(ceiling, 1).
arithmetic_functor(floor, 1).
arithmetic_functor(round, 1).
arithmetic_functor(truncate, 1).
arithmetic_functor(+, 2).
arithmetic_functor(-, 2).
arithmetic_functor(*, 2).
arithmetic_functor(/, 2).
arithmetic_functor(//, 2).
arithmetic_functor(mod, 2).
arithmetic_functor(rem, 2).
arithmetic_functor(min, 2).
arithmetic_functor(max, 2).
arithmetic_functor(**, 2).
arithmetic_functor(^, 2).

compile_argument(Expression, Functions, Options, Value, Goals) :-
    (   module_function(Expression, _, _)
    ;   string_concat_expression(Expression, _, _)
    ;   list_concat_expression(Expression, _, _)
    ;   atom_concat_expression(Expression, _, _)
    ;   declared_function_call(Expression, Functions, _)
    ),
    !,
    starlog_expression(Expression, Value, Functions, Options, Goals).
compile_argument(Expression, Functions, Options, Value, Goals) :-
    arithmetic_expression(Expression),
    !,
    compile_arithmetic(Expression, Functions, Options, Value, Goals).
compile_argument(Expression, _, _, Expression, []) :-
    (   var(Expression)
    ;   atomic(Expression)
    ),
    !.
compile_argument(Expression, _, _, Expression, []) :-
    nonvar(Expression),
    Expression = [_|_],
    !.
compile_argument(Expression, _, _, _, _) :-
    callable(Expression),
    !,
    functor(Expression, Name, Arity),
    throw(error(existence_error(starlog_function, Name/Arity), _)).
compile_argument(Expression, _, _, _, _) :-
    throw(error(domain_error(starlog_expression, Expression), _)).

compile_arithmetic(Expression, _, _, Expression, []) :-
    (   var(Expression)
    ;   number(Expression)
    ),
    !.
compile_arithmetic(Expression, Functions, Options, Value, Goals) :-
    Expression =.. [Functor|Arguments],
    maplist(compile_argument_with(Functions, Options),
            Arguments, Values, GoalLists),
    append(GoalLists, Goals),
    Value =.. [Functor|Values].

compile_argument_with(Functions, Options, Expression, Value, Goals) :-
    compile_argument(Expression, Functions, Options, Value, Goals).

ensure_text_operand(Operand, Options) :-
    (   memberchk(coerce(true), Options)
    ->  true
    ;   atomic(Operand),
        ground(Operand),
        \+ string(Operand)
    ->  throw(error(type_error(string, Operand), _))
    ;   true
    ).

ensure_atom_operand(Operand, Options) :-
    (   memberchk(coerce(true), Options)
    ->  true
    ;   atomic(Operand),
        ground(Operand),
        \+ atom(Operand)
    ->  throw(error(type_error(atom, Operand), _))
    ;   true
    ).

text_arguments(Left, Right, Options, Goals, TextLeft, TextRight) :-
    (   memberchk(coerce(true), Options)
    ->  Goals = [mnn_starlog:coerce_text(Left, TextLeft),
                 mnn_starlog:coerce_text(Right, TextRight)]
    ;   Goals = [],
        TextLeft = Left,
        TextRight = Right
    ).

atom_arguments(Left, Right, Options, Goals, AtomLeft, AtomRight) :-
    (   memberchk(coerce(true), Options)
    ->  Goals = [mnn_starlog:coerce_atom(Left, AtomLeft),
                 mnn_starlog:coerce_atom(Right, AtomRight)]
    ;   Goals = [],
        AtomLeft = Left,
        AtomRight = Right
    ).

coerce_text(Value, Text) :-
    (   string(Value)
    ->  Text = Value
    ;   term_string(Value, Text)
    ).

coerce_atom(Value, Atom) :-
    (   atom(Value)
    ->  Atom = Value
    ;   term_string(Value, Text),
        atom_string(Atom, Text)
    ).

goals_conjunction([Goal], Goal) :-
    !.
goals_conjunction([Goal|Goals], conj(Goal, Rest)) :-
    goals_conjunction(Goals, Rest).

reverse_predicates([], _, []).
reverse_predicates(
    [mnn_pred(Key, Modes, Domains, Clauses, Status)|Predicates],
    Functions,
    [mnn_pred(Key, Modes, Domains, StarlogClauses, Status)|Starlog]) :-
    reverse_clauses(Clauses, Functions, StarlogClauses),
    reverse_predicates(Predicates, Functions, Starlog).

reverse_clauses([], _, []).
reverse_clauses(
    [mnn_clause(Id, Head, Body, Location)|Clauses],
    Functions,
    [mnn_clause(Id, Head, StarlogBody, Location)|Starlog]) :-
    reverse_goal(Body, Functions, StarlogBody),
    reverse_clauses(Clauses, Functions, Starlog).

reverse_goal(conj(Left, Right), Functions, conj(NewLeft, NewRight)) :-
    !,
    reverse_goal(Left, Functions, NewLeft),
    reverse_goal(Right, Functions, NewRight).
reverse_goal(disj(Left, Right), Functions, disj(NewLeft, NewRight)) :-
    !,
    reverse_goal(Left, Functions, NewLeft),
    reverse_goal(Right, Functions, NewRight).
reverse_goal(ite(If, Then, Else), Functions, ite(NewIf, NewThen, NewElse)) :-
    !,
    reverse_goal(If, Functions, NewIf),
    reverse_goal(Then, Functions, NewThen),
    reverse_goal(Else, Functions, NewElse).
reverse_goal(not(Goal), Functions, not(NewGoal)) :-
    !,
    reverse_goal(Goal, Functions, NewGoal).
reverse_goal(once(Goal), Functions, once(NewGoal)) :-
    !,
    reverse_goal(Goal, Functions, NewGoal).
reverse_goal(is(Output, Expression), Functions, is(Output, NewExpression)) :-
    !,
    reverse_arithmetic_expression(Expression, Functions, NewExpression).
reverse_goal(string_concat(Left, Right, Output), _, is(Output, :(Left, Right))) :-
    !.
reverse_goal(append(Left, Right, Output), _, is(Output, '&'(Left, Right))) :-
    !.
reverse_goal(atom_concat(Left, Right, Output), _, is(Output, '•'(Left, Right))) :-
    !.
reverse_goal(Goal, _, StarlogGoal) :-
    module_predicate_call(Goal, Module, Call, Output),
    !,
    StarlogGoal = is(Output, Module:Call).
reverse_goal(Goal, Functions, is(Output, Call)) :-
    declared_predicate_call(Goal, Functions, Call, Output),
    !.
reverse_goal(Goal, _, Goal).

reverse_arithmetic_expression(Expression, Functions, StarlogExpression) :-
    (   module_function(Expression, Module, Call)
    ->  reverse_function_expression(Module:Call, Functions,
                                    StarlogExpression)
    ;   declared_function_call(Expression, Functions, Call)
    ->  reverse_function_expression(Call, Functions, StarlogExpression)
    ;   Expression =.. [Functor|Arguments],
        arithmetic_functor(Functor, Arity),
        length(Arguments, Arity)
    ->  maplist(reverse_arithmetic_argument(Functions),
                Arguments, StarlogArguments),
        StarlogExpression =.. [Functor|StarlogArguments]
    ;   StarlogExpression = Expression
    ).

reverse_arithmetic_argument(Functions, Expression, StarlogExpression) :-
    reverse_arithmetic_expression(Expression, Functions, StarlogExpression).

reverse_function_expression(Module:Call, _, Module:Call) :-
    !.
reverse_function_expression(Call, _, Call).

module_predicate_call(Goal, Module, Call, Output) :-
    nonvar(Goal),
    Goal = Module:Predicate,
    atom(Module),
    compound(Predicate),
    Predicate =.. [Name|Arguments],
    append(Inputs, [Output], Arguments),
    Inputs \= [],
    Call =.. [Name|Inputs].

declared_predicate_call(Goal, Functions, Call, Output) :-
    compound(Goal),
    Goal =.. [Name|Arguments],
    append(Inputs, [Output], Arguments),
    length(Inputs, Arity),
    memberchk(Name/Arity, Functions),
    Call =.. [Name|Inputs].

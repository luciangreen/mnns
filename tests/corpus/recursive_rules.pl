:- module(recursive_rules, [ancestor/2, sum_list/2]).

parent(ada, ben).
parent(ben, cy).
parent(ada, dee).

ancestor(Ancestor, Descendant) :-
    parent(Ancestor, Descendant).
ancestor(Ancestor, Descendant) :-
    parent(Ancestor, Intermediate),
    ancestor(Intermediate, Descendant).

sum_list([], 0).
sum_list([Head|Tail], Sum) :-
    sum_list(Tail, Rest),
    Sum is Head + Rest.

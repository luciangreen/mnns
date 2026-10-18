:- module(strings_and_terms, [label/2, nested_term/2]).

label(Name, "hello, world") :-
    Name = 'sample item'.

nested_term([Head|Tail], pair(Head, Tail)).

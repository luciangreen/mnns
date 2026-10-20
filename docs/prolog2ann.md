# Prolog-to-ANN front end (M1)

This milestone adds the parser and normalizer for the planned Prolog-to-ANN
converter. It does not yet ground programs or generate, execute, train, or
export a neural network.

## Parsing

`prolog2ann_parse:parse_file/3` reads a `.pl` source file and either `none` or a
domain-file path:

```prolog
?- use_module('prolog/prolog2ann/parse').
?- use_module('prolog/prolog2ann/normalise').
?- prolog2ann_parse:parse_file('examples/ancestor.pl', none, Parsed),
   prolog2ann_normalise:normalize_program(Parsed, Program).
```

The parser returns `ann_source(SourceFile, Clauses, Domains)`. Each clause is
represented as
`ann_clause(Id, Head, Body, VariableNames, File, Line)`. Variable identity is
preserved between the head, body, and `VariableNames`, and source locations are
one-based. Module declarations are ignored; other directives are rejected.

Domain files contain only ground finite-domain and integer-range declarations:

```prolog
domain(person, [ann, bob, cy]).
range(n, 0, 20).
```

The parser checks their shape and returns the declarations for later stages.
It does not use them to ground clauses yet.

## Normalization and negation

`prolog2ann_normalise:normalize_program/2` returns
`ann_program(SourceFile, Clauses, Domains)`. It splits disjunctions into
alternative clauses, flattens conjunctions into goal lists, converts `\+ Goal`
to `not(Goal)`, and moves supported arithmetic and comparison goals to the end
of each body while retaining their relative order.

Negated goals must be individual atoms. The normalizer builds predicate
dependencies and rejects a negative dependency if its target can reach the
head predicate; the exception includes the involved predicate-indicator cycle:

```prolog
error(non_stratified_negation([p/1, q/1, p/1]), file('source.pl', 4))
```

Supported built-ins are truth/failure, unification and term comparisons, `is/2`,
and finite-integer arithmetic comparisons. The parser rejects cut, dynamic
database updates, I/O, meta-calls, collection predicates, and other recognized
system predicates outside this subset with
`error(unsupported_construct(Construct), file(File, Line))`. Unknown callable
goals are treated as user predicates; resolution and safety checking belong to
later stages.

Run the full test suite, including front-end tests, with:

```sh
swipl -q -s tests/run.pl
```

## Milestone status

This is M1 only (FR-1 to FR-3). Finite-domain grounding, Herbrand-base limits,
translation, runtime queries, sigmoid training, extraction, and JSON export
remain future milestones.

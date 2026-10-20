# Prolog-to-ANN decisions

## M1 parser and normalizer

- Input module declarations are ignored; other source directives are rejected
  rather than executed or silently discarded.
- The optional domain file accepts only ground `domain/2` and integer `range/3`
  facts. The parser validates and returns these declarations; grounding is
  deferred to M2.
- Parsed clauses use
  `ann_clause(Id, Head, Body, VariableNames, File, Line)`. Disjunction
  alternatives receive IDs of the form `OriginalId-AlternativeNumber`.
- Negation is restricted to one callable goal and represented as `not(Goal)`.
  A negative dependency is non-stratified exactly when its target can reach the
  source predicate in the full dependency graph; the reported cycle includes
  the repeated starting predicate.
- Arithmetic and comparison goals are stably moved to the end of each
  normalized body. This is the staged grounding contract; the front end does
  not claim to preserve arbitrary operational Prolog behavior.
- Unknown callable goals are treated as user predicates. Recognized system
  predicates outside the accepted pure subset and the constructs listed in
  `pr1.txt` are rejected with source locations.

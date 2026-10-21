# Starlog — readable function view

`mnn_starlog:starlog_to_ir/2` translates Starlog expressions in an
`mnn_program/5` IR program into ordinary Prolog goals. The input program can be
created with `mnn_ir:parse_program/2`; `ir_to_starlog/2` converts the supported
IR forms back to the readable view. Program metadata, clause order, proof,
trace, and source locations are preserved.

## Supported forms

An expression `Output is Function(Inputs)` becomes a predicate call with the
output appended as its final argument. A function must either be declared by a
`:- starlog_function(Name/Arity)` directive or be module-qualified. For example,
`Result is twice(Value)` becomes `twice(Value, Result)` when `twice/1` is
declared, and `Result is lists:reverse(List)` becomes
`lists:reverse(List, Result)`. Module qualification is checked before the
Starlog string operator, so `lists:reverse/1` is not parsed as concatenation.

The supported operators are:

| Expression | Generated Prolog goal |
| --- | --- |
| `Left:Right` | `string_concat(Left, Right, Output)` |
| `Left & Right` | `append(Left, Right, Output)` |
| `Left • Right` | `atom_concat(Left, Right, Output)` |

The IR reader recognizes `&` and `•` in source terms. `:` is already a Prolog
operator; a compound right operand with an atom on the left is treated as module
qualification, while other `:` terms are string concatenation.

Ordinary whitelisted arithmetic expressions remain `is/2` expressions.
Undeclared, unqualified compound functions are rejected with
`existence_error(starlog_function, Name/Arity)` rather than being silently
interpreted as arithmetic.

## Type checks and coercion

The default `starlog_to_ir/2` requires known ground operands of `:` to be
strings and known ground operands of `•` to be atoms. A known mismatch such as
`2:"a"` raises `type_error(string, 2)`. Non-ground operands are checked by the
generated `string_concat/3` or `atom_concat/3` call when the program runs.

Explicit text/atom coercion is available through the optional third argument:

```prolog
mnn_starlog:starlog_to_ir(Program, [coerce(true)], IRProgram).
```

Coercion converts values using `term_string/2`; emitted code calls
`mnn_starlog:coerce_text/2` or `mnn_starlog:coerce_atom/2`. To run an emitted
coercing program in a fresh Prolog process, load this module as well.

## Limits

This is a readable view, not a general Prolog-to-Starlog parser or evaluator.
Function expressions are supported in `is/2` goals, including within the
whitelisted arithmetic expression grammar. The reverse view treats
`string_concat/3`, `append/3`, and `atom_concat/3` as the corresponding Starlog
operators, and treats declared or module-qualified predicates with a final
output argument as functions. Arbitrary predicate calls may therefore be
ambiguous under reverse conversion. S2A recursive/list generalization, formal
example-reproduction proofs, and the broader Starlog language remain future
work.

## Tests

Run the focused Starlog tests from the repository root:

```sh
swipl -q -g "load_files('tests/starlog_tests.pl'), run_tests(mnn_starlog), halt"
```

Run the complete suite, including Starlog:

```sh
swipl -q -s tests/run.pl
```

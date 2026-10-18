# Proof rules

The checker supports `identity`, restricted `reorder_goals` and
`introduce_definition`, and narrowly scoped `unfold` and `fold` rules. It
certifies these transformations directly from the IR, without executing either
program.

The accepted proof shape is:

```prolog
proof([
    proof_step(1, identity, [],
               equivalent(domain(Domain), modes(Modes)))
])
```

`Domain` and `Modes` are ground annotations supplied by the proof author. Since
the identity rule proves equality of the complete programs, it is sound for any
such annotations. The checker compares programs with variant equivalence, so
renamed clause variables are accepted while changed clauses are rejected.
The `reorder_goals` rule uses the same proof-step shape:

```prolog
proof([
    proof_step(1, reorder_goals, [],
               equivalent(domain(Domain), modes(Modes)))
])
```

For this rule, `Original` is the source program and `Program` is the proposed
result. The checker accepts only if it can derive the result by swapping exactly
one adjacent pair of conjunction goals in one clause body. Both goals must be
ground calls to one of `atom/1`, `atomic/1`, `compound/1`, `ground/1`,
`integer/1`, `is_list/1` or `number/1`, with a ground argument. These built-ins
are pure and do not bind variables or raise instantiation errors in this
restricted use, so their order does not affect answers. The checker rejects
variable-bearing goals, other predicates, extra changes, and unsupported proof
rules. Domain and mode annotations must be ground, but this restricted rule does
not infer them.

The unfold and fold rules use the same proof-step shape, with `unfold` or `fold`
as the rule name. They accept exactly one occurrence change in one clause body.
The checker requires a matching single-clause definition. Ground heads with
ground bodies remain supported when the body consists only of `true`, `fail`,
the listed pure unary tests, and conjunctions or disjunctions of those goals.
It also supports unary variable heads such as `positive(X)` when the body uses
only `true`, `fail`, or those same pure unary tests applied to that head
argument, composed with conjunction or disjunction. Unfold instantiates such a
body from the matched call. Fold requires the occurrence to be a variant of the
variable-bearing body, so it cannot introduce variable aliasing. Both rules
exclude cuts, meta-calls, and side effects, and do not implement general
unfold/fold checking.

`introduce_definition` accepts one change that replaces a ground goal composed
only of the listed pure unary tests, `true`, `fail`, conjunction, or disjunction
with a fresh zero-arity helper predicate whose sole clause contains that goal.
It also accepts a goal over exactly one variable when it consists only of `true`,
`fail`, or the listed pure unary tests applied to that same variable, composed
with conjunction or disjunction. This is factored into a fresh unary helper; the
caller passes the variable through, and the generated helper clause uses a fresh
variable shared only between its head and body. The helper name and clause ID are
generated without colliding with existing predicates or clauses. This limited
rule does not infer general purity or determinism and does not support goals over
multiple variables.

The checker still does not implement general purity/determinism analysis,
general clause/goal reordering, or the other rules in §7.2. Domain and mode
annotations must be ground but are not inferred. `render_proof/4` reports the
independent checker's result and summarizes accepted identity, goal-reordering,
definition-introduction, unfold, and fold steps. Rendering is explanatory and
does not itself certify a proof.

`mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown)` renders a
Markdown report and includes the independent checker's result. Accepted identity
proofs are explained as alpha-equivalence of the complete IR terms; rejected or
unsupported proofs are shown as quoted Prolog terms and are clearly marked as
rejected.

Several checked rewrites may be composed in one proof by listing their steps in
order. For a multi-step proof, each step is independently validated against the
IR produced by the preceding step; every step must be a supported rule with
ground domain and mode annotations. The final IR must be alpha-equivalent to
`Program`. This permits checked rewrite chains without treating a later step as
evidence for an earlier one.

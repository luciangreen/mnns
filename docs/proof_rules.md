# Proof rules

The initial checker supports one proof rule: `identity`. It certifies that an
MNN program and its original are alpha-equivalent, without executing either
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
Proofs containing other rules are rejected until an independent checker for
those rules is implemented. In particular, this subset does not certify any
program rewrite.

`mnn_proof_renderer:render_proof(Program, Original, Proof, Markdown)` renders a
Markdown report and includes the independent checker's result. Accepted identity
proofs are explained as alpha-equivalence of the complete IR terms; rejected or
unsupported proofs are shown as quoted Prolog terms and are clearly marked as
rejected. Rendering is explanatory and does not itself certify a proof.

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

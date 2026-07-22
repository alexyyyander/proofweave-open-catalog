# Jacobian counterexample algebraic audit

This source-pinned Lean workspace reproduces one bounded part of the public
three-dimensional Jacobian announcement: a displayed polynomial map has
constant Jacobian determinant `-2` and three distinct rational preimages of one
point.

It intentionally does not label the whole Jacobian Conjecture as independently
reviewed or settled. See `SOURCE.md` for the exact claim boundary.

Run locally with:

```sh
lake update
lake env lean ProofweaveJacobian.lean
```


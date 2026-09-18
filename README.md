# JSP-000760 / Erdős Problem 916

Complete Lean 4 formalization of Thomassen's theorem: every finite simple
graph with `n` vertices and at least `2n - 2` edges contains a cycle and a
vertex outside it adjacent to three distinct vertices on the cycle.

The Lean statement assumes `2 <= n`. This is necessary because subtraction on
`Nat` is truncated: without the assumption, the literal formula has a false
`n = 1` instance (`2 * 1 - 2 = 0`). The nontrivial theorem is unchanged.

## Build

```sh
lake update
lake build
```

## Proof structure

The formalization includes:

- the faithful cycle-and-three-spokes predicate;
- preservation under adding edges and under injective graph homomorphisms;
- the fact that the configuration needs at least four vertices;
- the exact `2n - 3` classification by triangles, `K₃,₃`, and 2-clique
  sums (cockades);
- the low-separation and 2-separation reductions;
- the acyclicity argument for the degree-three subgraph;
- the ear and augmented-graph argument which eliminates every core on at least
  seven vertices;
- the final extremal deduction for graphs with at least `2n - 2` edges.

`JSP000760.lean` is the public interface. The complete proof is in
`JSP000760/Proof.lean`, and `Check.lean` performs the axiom audit.

## Verification

Tested with Lean `v4.31.0` and Mathlib `v4.31.0`. `lake build` succeeds.
The source contains no `sorry`, `admit`, custom `axiom`, or `native_decide`.
The public theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

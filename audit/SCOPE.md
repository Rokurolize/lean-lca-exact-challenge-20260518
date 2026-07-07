# Scope

Mode: formal audit / corrective formalization continuation.

Target: the `LeanLCAExactChallenge` Lean 4 project, specifically the exact-category acyclicity and bounded-derived-category layer for `MetrizableLCA`.

Known blocker: the legacy predicate

```lean
exactAcyclic C K := ∀ i, QuillenExactCategory.Conflation (K.sc i)
```

makes each adjacent pair of differentials itself a conflation. That is a degreewise short-complex condition, not the usual exact-category acyclicity of a complex through cycle objects. In `MetrizableLCA`, treating each differential as both the deflation of one conflation and the inflation of the next is too strong and collapses the intended mathematics.

Corrective target: introduce a Lean-native exact-category acyclicity predicate with explicit cycle objects `Z^i`, maps `Z^i -> K^i` and `K^i -> Z^(i+1)`, a conflation `Z^i -> K^i -> Z^(i+1)` for each degree, and a factorization of the differential through these cycle objects.

Properties to verify in this pass:

1. The new predicate states the correct cycle-object exactness data directly.
2. The specialized `MetrizableLCA` version is equivalent to using `challengeExactSequence` on those cycle-object short complexes.
3. The corrected bounded weak equivalence predicate uses the corrected mapping-cone acyclicity, without relying on the legacy degreewise condition.

Assumptions and constraints:

- The supplied offline bundle is the source of truth.
- No network access is assumed.
- The existing legacy route is not globally replaced in this pass; it is isolated and a replacement predicate/localizer is added so later refactors can migrate theorem-by-theorem.
- Remaining old theorems about `exactAcyclic` are treated as compatibility artifacts, not as the corrected derived-category construction.

Out of scope in this pass:

- Reproving the full Verdier/localization stack against the new predicate.
- Replacing every theorem that currently mentions the legacy `exactAcyclic`.
- Proving nontrivial closure properties of the new predicate under cones, shifts, and biproducts.

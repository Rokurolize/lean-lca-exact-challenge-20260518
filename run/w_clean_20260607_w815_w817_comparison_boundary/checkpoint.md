# W815-W817 Comparison Boundary Checkpoint

## Scope

This checkpoint exposes the existing W815-W817 comparison-topology, bijective-embedding, and comparison-isomorphism route declarations in the Required and Original Four audit surfaces. It does not alter the route theorem bodies and does not claim product success.

## Changed Files

- `audit/RequiredDeclarations.lean`
- `audit/OriginalFourTaskCompletionDeclarations.lean`
- `run/goal_identity_20260602_human_centered_positive_witness.json`
- `run/w_clean_20260607_w815_w817_comparison_boundary/*`

## Boundary Exposed

- W815: projection-topology facts for left/right homology data, including open and surjective quotient projections and closed-embedding kernel inclusions.
- W816: reduction from bijective embedding of the canonical comparison map to the W814 bijective-open target and `CategoryWithHomology MetrizableLCA`.
- W817: reduction from categorical `IsIso` of the canonical comparison map to the W816 bijective-embedding target and the W816 category-with-homology bridge.

## Nonterminal Status

The checked W815-W817 route states still carry `productSuccessClaimed := false`. This checkpoint only improves audit visibility for already-proved comparison-boundary declarations.

## Verification

- `lake env lean LeanLCAExactChallenge/Derived/ComparisonProjectionTopologyRoute.lean`
- `lake env lean LeanLCAExactChallenge/Derived/ComparisonBijectiveEmbeddingRoute.lean`
- `lake env lean LeanLCAExactChallenge/Derived/ComparisonIsomorphismEmbeddingRoute.lean`
- `lake build LeanLCAExactChallenge.Derived.ComparisonIsomorphismEmbeddingRoute`
- `lake env lean audit/RequiredDeclarations.lean`
- `lake env lean audit/ProductSuccessDeclarations.lean`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check -- ...`
- Forbidden-token, declaration-presence, warning/error, false-nonclaim, true-boolean, and goal-identity scans are recorded in this directory.

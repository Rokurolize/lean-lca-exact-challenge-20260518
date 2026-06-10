# W923/W601 Target-Difference Bridge Checkpoint

- generated_utc: 2026-06-10T01:07:43Z
- base_head: 71ac45395b881d40a9451c953e498936075053b0
- product_success: false
- product_complete: false
- update_goal_allowed: false

This checkpoint does not complete the original four-task positive witness. It removes W923 as a separate frontier by proving that its primitive preimage quantifier is just the existing ordinary target-difference `Function.Surjective` statement, and that the primitive provider can be obtained from W713 or from W601 specialized to the identity closed embedding.

## Source Changes

`LeanLCAExactChallenge/Derived/ClosedMapTargetSurjectivePrimitiveFieldRoute.lean` now contains:

```lean
def Dbounded.targetDifferenceSurjectivePrimitiveOfSurjectiveW923
def Dbounded.targetDifferenceSurjectivePrimitiveOfTargetProviderW923
def Dbounded.targetDifferenceSurjectivePrimitiveOfTargetDifferenceProviderW601
```

The W601 bridge uses `Topology.IsClosedEmbedding.id` on `(𝟙 Y).app j`, so it does not add a mathematical assumption. It only specializes the older closed-embedding-indexed provider to the identity component.

`LeanLCAExactChallenge/Derived/ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean` now contains:

```lean
def Dbounded.targetNoUnivDataOfTargetDifferenceProviderAndCompactSpaceProviderW944
```

This composes the W601 target-difference bridge with the existing W930 compact-space-to-no-univ bridge.

## Verification

- `lake env lean run/w923_w601_target_difference_bridge_probe_20260609.lean`: passed.
- `lake build LeanLCAExactChallenge.Derived.ClosedMapTargetSurjectivePrimitiveFieldRoute`: passed.
- `lake build LeanLCAExactChallenge.Derived.ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute`: passed.
- `lake build`: passed.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge`: passed.
- `lake env lean audit/RequiredDeclarations.lean`: passed.
- `lake env lean audit/ProductSuccessDeclarations.lean`: passed.
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean`: passed.
- Declaration-shaped product-success and original-four-task completion scans: passed with empty logs.
- `git diff --check`: passed.

## Remaining Frontier

The target side is now expressed through canonical W601/W713 provider surfaces. The source still does not construct a nullary `TargetDifferenceSurjectiveProviderW601`, `TargetDifferenceSurjectiveForTargetProviderW713`, or `TargetCodomainCompactSpaceProviderW601` for arbitrary target diagrams. Those arbitrary statements are not true without additional diagram-specific hypotheses or a restricted target class.

The original product witness remains blocked on the broader W987/W1450 provider chain and the final bounded-derived stable package. The next source step should construct a mathematically honest target-difference/compactness provider for the actual target diagrams in scope, restrict the target API to a true hypothesis, or continue eliminating W987/W1450 through stronger route theorems.

# W992 Provider Search Ledger

Generated: 2026-05-27 13:54 JST

## Decision

W992 replaces W991's W944 target no-univ data input with W715 target surjective-compact data. This derives the W930 filter nonbottom compactness primitive from `CompactSpace` using compact cluster points, while projecting target-difference surjectivity directly from W715.

## Candidate Surfaces

- `TargetSurjectiveNoUnivMembershipForTargetProviderW944`: rejected as the terminal W992 input because W991 already consumes it opaquely.
- `TargetSurjectiveCompactForTargetProviderW715`: selected because it supplies the same target-difference surjectivity and a structural `CompactSpace` field strong enough to prove W930's nonbottom filter condition by `isCompact_univ.exists_clusterPt`.
- Raw W930 target-codomain no-univ membership primitive: rejected as a terminal W992 input because it is exactly the filter-style condition now derived from compactness.
- W947/W725 target/closedness data: rejected because those surfaces would widen the branch-specific W973 closed-embedding closedness input back to the older closed-map-or-closed-embedding closedness boundary.

## Result

`ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromKernelCokernelTopIsoComponentFieldsRoute.lean` constructs:

- `targetNoUnivDataOfTargetSurjectiveCompactW992`
- `w991LeavesOfTargetSurjectiveCompactW992`
- `fullDataOfTargetSurjectiveCompactW992`
- `w981LeavesOfTargetSurjectiveCompactW992`
- `componentFieldsOfTargetSurjectiveCompactW992`
- delegates through W991/W990/W989/W988/W987 to the stable ExactAt route

Product success remains false. The remaining W992 surface still has 13 explicit Lean input names, but the target input is now W715 target surjective-compact data instead of W944 target no-univ filter data.

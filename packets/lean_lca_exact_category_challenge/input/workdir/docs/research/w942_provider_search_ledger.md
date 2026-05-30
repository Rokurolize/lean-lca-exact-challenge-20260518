# W942 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T173426Z_codex_parent_w942_closedness_data_boundary_relation_route`

Baseline: W941 commit `4b9bb6a`, with product success still false and 16 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| W725 closedness branch data | Replace W941's selected-difference pi1/pi2/pi3 primitive closed-map leaves and mapped-cokernel primitive closed-map leaf with one `MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725` field | W725 already aligns selected-difference component closedness with the matching W519 mapped-explicit-cokernel closedness provider. Its closed-map branch projects directly to the W941 primitive leaves; its closed-embedding branch supplies closed-map leaves via `IsClosedEmbedding.isClosedMap` | Selected for W942. |
| W718 selected-difference component provider plus W519 mapped-cokernel provider | Replace the four primitive leaves with two separate provider fields | This is valid but less aligned than W725, which preserves the closed-map/closed-embedding branch relationship in one semantic provider | Deferred. |
| Target surjective-compact W715 provider | Replace target-difference and target-codomain compactness leaves with `TargetSurjectiveCompactForTargetProviderW715` | W941's target-codomain leaf is the W930 no-univ-membership filter primitive, not the older `CompactSpace` provider surface. No direct W715-to-W930 adapter was selected in this pass | Deferred. |
| Concrete closedness proofs | Eliminate selected-difference or mapped-cokernel closedness assumptions entirely | No no-argument construction was identified; W942 restores the existing W725 provider boundary and does not instantiate it | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetCompactNoUnivMembershipClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`.

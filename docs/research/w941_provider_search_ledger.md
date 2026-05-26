# W941 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T172058Z_codex_parent_w941_boundary_relation_data_normalized_strict_representative_lift_route`

Baseline: W940 commit `28e27fd`, with product success still false and 18 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| W716 boundary data | Replace W940's separate right-open closed-quotient-cover boundary and source-difference cokernel-pi-zero boundary leaves with one `MetrizableWppLimitBoundaryDataW716` field | `WppOpExactAcyclicProjectionFields.lean` defines `rightOpenBoundary_of_boundaryDataW716` and `sourcePiZeroBoundary_of_boundaryDataW716`; W902 already uses the same projection pattern | Selected for W941. |
| W717 relation data | Replace W940's separate relation-pullback and target-relation-lift providers with one `ClosedNatTransOrdinaryRelationDataProviderW717` field | `WppOpExactAcyclicProjectionFields.lean` defines `relationPullbackProvider_of_relationDataW717` and `targetRelationLiftsProvider_of_relationDataW717`; W903 already uses the same projection pattern | Selected for W941. |
| Target surjective and target compact data | Replace target-difference surjectivity plus target-codomain compactness with a higher-level provider | Existing W715-era providers bundle target data before the no-univ-membership primitive refinement; no direct provider was identified that preserves the current W930 no-univ-membership target surface | Deferred. |
| Selected-difference plus mapped-cokernel closedness data | Replace four selected-difference and mapped-cokernel primitive fields with a W725-style closedness provider | Existing W725 data is useful in older comparison routes, but W940 currently uses W921/W922 primitive no-univ-membership branch fields; a direct adapter was not selected in this pass | Deferred. |
| No-argument boundary or relation proof construction | Eliminate boundary or relation assumptions entirely | No concrete no-argument construction was identified; W941 only restores existing semantic provider boundaries and does not instantiate the providers | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetCompactNoUnivMembershipBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`.

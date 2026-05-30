# W940 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T165943Z_codex_parent_w940_normalized_strict_representative_lift_route`

Baseline: W939 commit `315d9f2`, with product success still false and 35 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| Normalized strict-representative lift blueprint | Replace W939's strict-preimage object fields, strict-preimage map fields, identity and composition coherence, and source-image object/map normalization with one `Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint` field | `BoundedFiniteProducts.lean` already defines the semantic normalized lift blueprint over `MetrizableWalkingParallelPairLiftBlueprint`; W890/W891/W892 show that these are the intended object-data, map-data, and coherence boundaries | Selected for W940. |
| Strict preimage object-only provider | Replace only the eight object fields with `MetrizableWalkingParallelPairStrictPreimageData` | This reduces fewer assumptions and still leaves map data, functorial coherence, and source-image normalization split across raw fields | Deferred. |
| W891/W892 comparison route reuse | Route through the older W890-W892 comparison leaves directly | Those leaves assume older bundled boundary, relation, target, closedness, endpoint, and localized-adjoint providers rather than the current W939 no-univ-membership endpoint-strict route surface | Deferred. |
| Target compactness or endpoint strict-exact construction | Replace a remaining W940 primitive proposition by a no-argument proof | No concrete construction was identified in this pass; these remain substantive mathematical obligations, not provider-boundary rewrites | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetCompactNoUnivMembershipNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`.

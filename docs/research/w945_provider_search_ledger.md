# W945 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T181041Z_codex_parent_w945_localized_unit_provider_route`

Baseline: W944 commit `69d19db`, with product success still false and 10 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| W945 localized-unit provider | Replace W944's localized right adjoint, localized adjunction, and strong unit mapping-cone strict-component witness with one provider `BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945` | W944 deferred raw W721 because W721 also carries `boundedHomotopyLocalizedUnitMem`. W945 avoids an extra assumption by deriving W721 unit membership from the stronger W939 component witness through the existing W936, W935, W933, W932, and W931 projection helpers | Selected for W945. |
| Raw W721 localized-right-adjoint data | Replace only the right adjoint and adjunction fields with W721 | W721's unit membership would be an additional weaker assumption unless it is derived from the stronger W939 witness. W945 proves that derivation and therefore uses a provider shaped around the actual W944 surface instead | Superseded by W945. |
| Endpoint-localized provider W726 | Bundle endpoint and localized-right-adjoint data together | W726 targets the older W720 endpoint strict-topology provider and would reintroduce endpoint forgetful homology preservation, while W944 carries an endpoint strict short-exact witness and a stronger unit-component witness | Deferred. |
| No-argument localized adjunction construction | Remove the localized right adjoint entirely | No current local route constructs the bounded-homotopy localized right adjoint and adjunction without an input. That remains a real task-4 construction gap, not a provider-boundary rewrite | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute.lean`.

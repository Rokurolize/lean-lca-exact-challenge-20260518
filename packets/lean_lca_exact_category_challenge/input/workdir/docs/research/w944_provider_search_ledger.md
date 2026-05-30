# W944 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T175756Z_codex_parent_w944_target_no_univ_provider_route`

Baseline: W943 commit `ac0c9d7`, with product success still false and 11 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| W944 target no-univ provider | Replace W943's target-difference surjectivity primitive and target-codomain no-univ compactness primitive with one provider `TargetSurjectiveNoUnivMembershipForTargetProviderW944` | W715 already establishes the local pattern of pairing target-difference surjectivity with target-codomain compactness for the older compact-space surface. W943 needs the newer W930 no-univ compactness surface, so W944 mirrors W715 without adding an extra compact-space or unit assumption | Selected for W944. |
| W715 target-surjective-compact provider | Reuse the older target provider directly | W715 projects to `CompactSpace`, while W943 consumes `targetCodomainCompactNoUnivMembershipPrimitiveW930`. No direct W715-to-W930 adapter was selected because the current surface needs filter nonbottom compactness data, not merely the older provider name | Deferred. |
| W721 localized-right-adjoint data | Replace the right adjoint and adjunction fields with W721 | W721 also contains a `unit_mem` field, while the current W943/W944 route carries the stronger component-level unit mapping-cone strict-exact witness. Introducing W721 here would add an unused assumption unless a direct projection from the stronger unit witness to W721 is proved | Deferred. |
| Existing W731 target/closedness/normalized/source/endpoint provider | Replace several remaining providers at once | W731 targets older W715/W720/W721/W724 provider surfaces, while W944 carries W930 no-univ target compactness, W722 source-triangulation data, endpoint strict-exact witnesses, and a stronger unit witness. Adapting W731 would be a larger route rewrite | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`.

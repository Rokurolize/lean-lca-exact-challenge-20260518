# W936 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T154929Z_codex_parent_w936_endpoint_short_exact_unit_strict_exact_witness_route`

Baseline: W935 commit `5606989b762599c957c34e2aa3663ac93e6bc121`, with product success still false and 39 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| Unit witness strict exact bridge | Replace the unit mapping-cone witness field from degreewise `QuillenExactCategory.Conflation` data to degreewise `MetrizableLCA.strictShortExact` data, then recover W935 through the strict exact-category instance | `MetrizableLCA.quillenExactCategory` defines conflations by `strictShortExact`; a focused W936 probe compiled with `simpa [MetrizableLCA.quillenExactCategory]` | Selected for W936. |
| Endpoint topology from endpoint `ShortExact` | Derive W935's endpoint closed-embedding/open-map fields directly from endpoint `ShortExact` | The available W935 `endpointShortExactOfExactAt` field provides categorical `ShortExact`, not the topological `IsClosedEmbedding` and `IsOpenMap` fields required separately by the current route | Deferred. |
| Strict preimage/source-image coherence | Construct or reduce the explicit strict representative object/map/coherence fields | W891-W892 expose these as raw fields; no direct construction from W935's current concrete data was identified in this pass | Deferred. |
| Relation primitive consolidation | Derive target relation lifts from relation pullback data | W920 keeps relation pullback and target relation lifts as distinct primitive witnesses; the lift provider is not an immediate consequence of the pullback equality in the current API | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetCompactNoUnivMembershipEndpointShortExactUnitStrictExactWitnessPrimitiveFieldRoute.lean`.

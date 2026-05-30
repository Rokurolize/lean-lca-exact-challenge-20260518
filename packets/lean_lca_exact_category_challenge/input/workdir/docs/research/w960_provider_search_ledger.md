# W960 Provider Search Ledger

Generated: 2026-05-27 06:06 JST

Baseline: W959 commit `348858a`, with product success still false and raw W722 source-triangulation fields feeding the W958 provider constructor.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Split W725 closed-map branch data | Replace the bundled W725 provider with `SelectedDifferenceClosedMapDiagramComponentProviderW718` and `MappedExplicitCokernelClosedMapProviderW519` | Exact fit for the W725 `closedMap` constructor and already matches earlier W896 branch evidence; W960 can construct W725 and reuse W959 | Selected for W960. |
| Split W725 closed-embedding branch data | Replace W725 with selected-difference closed-embedding components and the mapped-cokernel closed-embedding provider | Also exact, but it is a separate branch and should be tracked as its own route rather than mixed into the closed-map constructor path. | Deferred. |
| Split endpoint strict-exact witnesses | Expose internal closed-embedding, open-map, and outgoing-epi strict-exact proofs | Useful, but W725 was the remaining branch provider that W959 intentionally deferred. | Deferred. |
| Split W939 unit component witnesses | Replace the bundled unit-component witness with lower-level component fields | Larger surface and better handled after the W725 branch split. | Deferred. |

Selected W960 outcome: `ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldsRoute.lean` constructs the W725 `closedMap` branch from raw selected-difference closed-map diagram components and the mapped explicit cokernel closed-map provider, then delegates through W959/W958/W957/W956/W955/W954/W953/W952. Product success remains false because the resulting W960 field surface still contains explicit assumptions for raw W716 boundary fields, raw W717 relation fields, raw W719 normalized fixed-target fields, raw W722 source-triangulation fields, target primitives, endpoint strict-exact witnesses, bounded-homotopy localized adjunction data, and W939 unit component witnesses; the W725 closed-embedding constructor is also a separate nonterminal branch.
